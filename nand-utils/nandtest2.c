#define PROGRAM_NAME "nandtest2"

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <getopt.h>

#include <asm/types.h>
#include "mtd/mtd-user.h"
#include "libmtd.h"
#include "common.h"

#define UNUSED(x) (void)(x)

static NORETURN void usage(int status)
{
    fprintf(status ? stderr : stdout,
        "usage: %s [OPTIONS] <device>\n\n"
        "  -h, --help           Display this help output\n"
        "  -V, --version        Display version information and exit\n"
        "  -m, --markbad        Mark blocks bad if they appear so\n"
        "  -p, --passes         Number of passes [default=1]\n"
        "  -r <n>, --reads=<n>  Read operation repeats time [default=3]\n"
        "  -s, --start          Start index of block [default=0]\n"
        "  -n, --blocks         number of blocks to test [default=flash blocks number]\n"
        "  -S, --info-only      Only print MTD information, no test\n",
        PROGRAM_NAME);
    exit(status);
}

typedef int (* loc_opr_t)(int index, void *data);
typedef int (* intvl_opr_t)(int a, int b, void *data);

static struct mtd_info_user meminfo;
static struct mtd_ecc_stats oldstats, newstats;
static struct nand_oobinfo oobinfo;
static int fd;
static int markbad;
static libmtd_t mtd_desc;
static struct mtd_dev_info mtd;
static unsigned char *oobbuf;
static unsigned char *bbt;
static bool info_only;

/**
 * How many time each read  will repeats.
 */
static int nr_reads = 3;

/**
 * Seed values each used for a block that generate contents of every page
 * in the block.
 */
static int *seeds;

static int make_pages_buf(size_t len, int seed, char **p)
{
    char *buf;

    if (! (buf = malloc(len))) {
        fprintf(stderr, "out of memory in %s\n", __func__);
        return -1;
    }
    for (size_t i = 0; i < len; i += meminfo.writesize) {
        srand(seed);
        for (size_t j = 0; j < meminfo.writesize / sizeof(int); j++) {
            int r = rand();
            memcpy(buf + i + j * sizeof(r), &r, sizeof(r));
        }
    }

    *p = buf;
    return 0;
}

/**
 * read back pages of [page_start, page_end] and check contents
 * of the pages are as what were wrote down.
 *
 * @page_start index of start page
 * @page_end index of end page
 * @data a seed value (int) that used to generate page contents.
 */
static int aligned_read_and_compare(int page_start, int page_end, void *data)
{
    int seed = (int)(long int)data;
    int n_pages = page_end - page_start + 1;
    size_t len = n_pages * meminfo.writesize;
    ssize_t n;
    char *buf, *rbuf;
    char str[200]; /* large enough and no check */
    int fail_cnt;

    if (make_pages_buf(len, seed, &buf)) exit(1);
    if (! (rbuf = malloc(len))) {
        fprintf(stderr, "out of memory in %s\n", __func__);
        exit(1);
    }

    printf("read page %d to %d\n", page_start, page_end);

    fail_cnt = 0;
    for (int i = 0; i < nr_reads; ++i) {
        memset(rbuf, 0, len);
        n = pread(fd, rbuf, len, page_start * meminfo.writesize);
        if (n == -1) {
            sprintf(str, "read error on pages [%d, %d]\n", page_start, page_end);
            perror(str);
            exit(1);
        } else if (n < len) {
            fprintf(stderr, "read error on pages [%d, %d]. len %ld actual %ld\n"
                    , page_start, page_end, sizeof(rbuf), n);
            exit(1);
        }

        if (ioctl(fd, ECCGETSTATS, &newstats)) {
            perror("ECCGETSTATS");
            close(fd);
            exit(1);
        }

        if (newstats.corrected > oldstats.corrected) {
            printf("%d bit(s) ECC corrected at pages %d to %d\n",
                    newstats.corrected - oldstats.corrected,
                    page_start, page_end);
            oldstats.corrected = newstats.corrected;
        }
        if (newstats.failed > oldstats.failed) {
            printf("ECC failed at pages %d to %d\n", page_start, page_end);
            oldstats.failed = newstats.failed;
            ++fail_cnt;
            continue;
        }

        if (memcmp(buf, rbuf, len)) {
            fprintf(stderr, "page contents read not same as written\n");
            ++fail_cnt;
            continue;
        }
    }

    free(buf);
    free(rbuf);

    return fail_cnt < nr_reads ? 0 : -1;
}

/**
 * Only for my concerned chip: Samsung 1GiB 3.3v
 */
static int scan_badblocks(void)
{
    int bb_cnt = 0;
    int err;

    printf("scanning bad blocks: ");
    for (int i = 0; i < mtd.eb_cnt; ++i) {
        /* bad block mark could be in 1st or 2st page */
        for (int j = 0; j < 2; ++j) {
            if (mtd_read_oob(mtd_desc, &mtd, fd,
                        i * mtd.eb_size + j * mtd.min_io_size,
                        mtd.oob_size, oobbuf)) {
                fprintf(stderr, "read oob failed at block %d page %d\n", i, j);
                return -1;
            }
            if (oobbuf[0] != 0xff) {
                if (! bb_cnt)
                    printf("%d", i);
                else
                    printf(", %d", i);
                if ((err = mtd_is_bad(&mtd, fd, i)) < 0) {
                    fprintf(stderr, "\nmtd_is_bad() failed\n");
                    return -1;
                }
                if (err != 1) {
                    fprintf(stderr, "\nbad block status mismatched between mtd and oob\n");
                    return -1;
                }
                bbt[i] = 1;
                ++bb_cnt;
                break;
            }
        }
    }

    if (bb_cnt) printf(" ttl %d\n", bb_cnt);

    if (oldstats.badblocks != bb_cnt) {
        fprintf(stderr, "bad blocks count mismatched between mtd and oob\n");
        return -1;
    }

    return 0;
}

static int erase_block(int block)
{
    struct erase_info_user er;

    er.start = block * meminfo.erasesize;
    er.length = meminfo.erasesize;

    printf("erasing block %d\n", block);
    if (ioctl(fd, MEMERASE, &er)) {
        perror("MEMERASE");
        return -1;
    }
    return 0;
}

static int random_tree_walk(int from, int to, loc_opr_t opr, void *data)
{
    int err;
    int hint;

    if (from > to) return 0;

    hint = (random() % (to - from + 1)) + from;

    if ((err = opr(hint, data))) return err;

    if ((err = random_tree_walk(hint + 1, to, opr, data))) return err;
    if ((err = random_tree_walk(from, hint - 1, opr, data))) return err;

    return 0;
}

static int random_tree_walk_with_intvl(int from, int to, intvl_opr_t opr, void *data)
{
    int err;
    int a, b;

    if (from > to) return 0;

    a = (random() % (to - from + 1)) + from;
    b = (random() % (to - a + 1)) + a;

    if ((err = opr(a, b, data))) return err;

    if ((err = random_tree_walk_with_intvl(b + 1, to, opr, data))) return err;
    if ((err = random_tree_walk_with_intvl(from, a - 1, opr, data))) return err;

    return 0;
}

/**
 * Write [page_start, page_end] that had already been
 * erased.
 *
 * @page_start index of start page
 * @page_end index of end page
 * @data a seed value (int) that used to generate page contents.
 */
static int aligned_write(int page_start, int page_end, void *data)
{
    int seed = (int)(long int)data;
    int n_pages = page_end - page_start + 1;
    size_t len = n_pages * meminfo.writesize;
    ssize_t n;
    char *buf;
    char str[200]; /* large enough and no check */

    if (make_pages_buf(len, seed, &buf)) return -1;

    printf("write page %d to %d. nr of pages %d\n",
            page_start, page_end, page_end - page_start + 1);
    n = pwrite(fd, buf, len, page_start * meminfo.writesize);
    if (n == -1) {
        sprintf(str, "write error on pages [%d, %d]\n", page_start, page_end);
        perror(str);
        exit(1);
    } else if (n < len) {
        fprintf(stderr, "write error on pages [%d, %d]. len %ld actual %ld\n"
                , page_start, page_end, sizeof(buf), n);
        exit(1);
    }

    free(buf);
    return 0;
}

static int scratch_block(int block)
{
    int page_start = block * (meminfo.erasesize / meminfo.writesize);
    int page_end = page_start + (meminfo.erasesize / meminfo.writesize) - 1;

    if (random_tree_walk_with_intvl(page_start, page_end, aligned_write,
                (void *)(long int)seeds[block]))
        return -1;
    if (random_tree_walk_with_intvl(page_start, page_end, aligned_read_and_compare,
                (void *)(long int)seeds[block]))
        return -1;

    return 0;
}

static int test_block(int block, void *nouse)
{
    UNUSED(nouse);

    if (bbt[block]) {
        printf("skip bad block %d\n", block);
        return 0;
    }
    if (! erase_block(block) && ! scratch_block(block))
        return 0;

    if (markbad) {
        printf("Mark bad block %d\n", block);
        if (ioctl(fd, MEMSETBADBLOCK, block * meminfo.erasesize)) {
            perror("MEMSETBADBLOCK");
            exit(1);
        }
        bbt[block] = 1;
    }
    return 0;
}

static void get_ecc_info(void)
{
    if (ioctl(fd, ECCGETSTATS, &oldstats)) {
        perror("ECCGETSTATS");
        close(fd);
        exit(1);
    }

    printf("ecc: corrections %d failures %d bad blocks %d bbt blocks %d\n",
            oldstats.corrected, oldstats.failed, oldstats.badblocks,
            oldstats.bbtblocks);

    if (scan_badblocks()) {
        fprintf(stderr, "bad blocks info mismatched between kernel and oob\n");
        exit(1);
    }
}

/*
 * Main program
 */
int main(int argc, char **argv)
{
    int nr_passes = 1;
    uint32_t block_start = 0;
    uint32_t block_nr = -1;
    int error = 0;

    for (;;) {
        static const char short_options[] = "hn:ms:p:r:VS";
        static const struct option long_options[] = {
            { "help", no_argument, 0, 'h' },
            { "version", no_argument, 0, 'V' },
            { "markbad", no_argument, 0, 'm' },
            { "passes", required_argument, 0, 'p' },
            { "start", required_argument, 0, 's' },
            { "blocks", required_argument, 0, 'n' },
            { "reads", required_argument, 0, 'r' },
            { "info-only", no_argument, 0, 'S' },
            {0, 0, 0, 0},
        };
        int option_index = 0;
        int c = getopt_long(argc, argv, short_options, long_options, &option_index);
        if (c == EOF)
            break;

        switch (c) {
        case 'h':
            usage(EXIT_SUCCESS);
        case 'V':
            common_print_version();
            exit(EXIT_SUCCESS);
            break;
        case '?':
            usage(EXIT_FAILURE);

        case 'm':
            markbad = 1;
            break;

        case 'p':
            nr_passes = atol(optarg);
            break;

        case 'r':
            nr_reads = atol(optarg);
            break;

        case 's':
            block_start = simple_strtoul(optarg, &error);
            break;

        case 'n':
            block_nr = simple_strtoul(optarg, &error);
            break;

        case 'S':
            info_only = true;
            break;

        }
    }
    if (argc - optind != 1)
        usage(EXIT_FAILURE);
    if (error)
        errmsg_die("Try --help for more information");

    fd = open(argv[optind], O_RDWR);
    if (fd < 0) {
        perror("open");
        exit(1);
    }

    if (ioctl(fd, MEMGETINFO, &meminfo)) {
        perror("MEMGETINFO");
        close(fd);
        exit(1);
    }

    if (block_nr == -1) block_nr = meminfo.size / meminfo.erasesize;

    if (block_start + block_nr > meminfo.size / meminfo.erasesize) {
        fprintf(stderr, "block positon out of range\n");
        exit(1);
    }

    if (ioctl(fd, MEMGETOOBSEL, &oobinfo)) {
        perror("MEMGETOOBSEL");
        close(fd);
        exit(1);
    }

    mtd_desc = libmtd_open();
    if (! mtd_desc) {
        fprintf(stderr, "can't initialize libmtd\n");
        close(fd);
        exit(1);
    }
    if (mtd_get_dev_info(mtd_desc, argv[optind], &mtd) < 0) {
        fprintf(stderr, "mtd_get_dev_info failed\n");
        close(fd);
        exit(1);
    }

    if (! (bbt = (unsigned char *)malloc(mtd.eb_cnt))) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    memset(bbt, 0, mtd.eb_cnt);

    if (meminfo.size != mtd.size || meminfo.erasesize != mtd.eb_size
            || meminfo.writesize != mtd.min_io_size) {
        fprintf(stderr, "info mismatched\n");
        exit(1);
    }

    if (! (oobbuf = malloc(mtd.oob_size))) {
        fprintf(stderr, "Could not allocate %d bytes for buffer\n",
            mtd.oob_size);
        exit(1);
    }

    printf("memory: type %u flags 0x%x size %u erasesize %u writesize %u oobsize %u\n",
            meminfo.type, meminfo.flags, meminfo.size, meminfo.erasesize,
            meminfo.writesize, meminfo.oobsize); 
    printf("mtd: size %lld eb_cnt %d eb_size %d min_io_size %d"
            " subpage_size %d oob_size %d bb_allowed %d\n",
            mtd.size, mtd.eb_cnt, mtd.eb_size, mtd.min_io_size,
            mtd.subpage_size, mtd.oob_size, mtd.bb_allowed);
    printf("oob: useecc %d eccbytes %u\n", oobinfo.useecc, oobinfo.eccbytes);

    get_ecc_info();

    if (info_only) return 0;

    if (! (seeds = malloc(mtd.eb_cnt * sizeof(int)))) {
        fprintf(stderr, "out of memory in allocating seeds series\n");
        exit(1);
    }

    for (int i = 0; i < nr_passes; ++i) {
        int *p = seeds;
        srand(time(NULL));
        for (int j = 0; j < mtd.eb_cnt; j++) *p++ = rand();

        srandom(time(NULL));
        random_tree_walk(block_start, block_start + block_nr - 1, test_block, NULL);
        printf("finished pass %d\n", i + 1);
    }

    get_ecc_info();
}
