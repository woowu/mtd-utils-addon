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
#include <stdbool.h>

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
        "  -p, --passes         Number of passes\n"
        "  -r <n>, --reads=<n>  Read & check <n> times per pass\n"
        "  -o, --offset         Start offset on flash\n"
        "  -l, --length         Length of flash to test\n"
        "  -k, --keep           Restore existing contents after test\n"
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
static bool *bbt;
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

    if (fail_cnt == nr_reads) {
        ; /* markbad */
    }

    return 0;
}

static int read_and_compare(loff_t ofs, unsigned char *data,
                unsigned char *rbuf)
{
    ssize_t len;
    int i;

    len = pread(fd, rbuf, meminfo.erasesize, ofs);
    if (len < meminfo.erasesize) {
        printf("\n");
        if (len)
            fprintf(stderr, "Short read (%zd bytes)\n", len);
        else
            perror("read");
        exit(1);
    }

    if (ioctl(fd, ECCGETSTATS, &newstats)) {
        printf("\n");
        perror("ECCGETSTATS");
        close(fd);
        exit(1);
    }

    if (newstats.corrected > oldstats.corrected) {
        printf("\n %d bit(s) ECC corrected at %08x\n",
                newstats.corrected - oldstats.corrected,
                (unsigned) ofs);
        oldstats.corrected = newstats.corrected;
    }
    if (newstats.failed > oldstats.failed) {
        printf("\nECC failed at %08x\n", (unsigned) ofs);
        oldstats.failed = newstats.failed;
    }

    printf("\r%08x: checking...", (unsigned)ofs);
    fflush(stdout);

    if (memcmp(data, rbuf, meminfo.erasesize)) {
        printf("\n");
        fprintf(stderr, "compare failed\n");
        for (i=0; i<meminfo.erasesize; i++) {
            if (data[i] != rbuf[i])
                printf("Byte 0x%x is %02x should be %02x\n",
                       i, rbuf[i], data[i]);
        }
        return 1;
    }
    return 0;
}

static int erase_and_write(loff_t ofs, unsigned char *data, unsigned char *rbuf,
               int nr_reads)
{
    struct erase_info_user er;
    ssize_t len;
    int i, read_errs = 0;

    printf("\r%08x: erasing... ", (unsigned)ofs);
    fflush(stdout);

    er.start = ofs;
    er.length = meminfo.erasesize;

    if (ioctl(fd, MEMERASE, &er)) {
        perror("MEMERASE");
        if (markbad) {
            printf("Mark block bad at %08lx\n", (long)ofs);
            ioctl(fd, MEMSETBADBLOCK, &ofs);
        }
        return 1;
    }

    printf("\r%08x: writing...", (unsigned)ofs);
    fflush(stdout);

    len = pwrite(fd, data, meminfo.erasesize, ofs);
    if (len < 0) {
        printf("\n");
        perror("write");
        if (markbad) {
            printf("Mark block bad at %08lx\n", (long)ofs);
            ioctl(fd, MEMSETBADBLOCK, &ofs);
        }
        return 1;
    }
    if (len < meminfo.erasesize) {
        printf("\n");
        fprintf(stderr, "Short write (%zd bytes)\n", len);
        exit(1);
    }

    for (i=1; i<=nr_reads; i++) {
        printf("\r%08x: reading (%d of %d)...", (unsigned)ofs, i, nr_reads);
        fflush(stdout);
        if (read_and_compare(ofs, data, rbuf))
            read_errs++;
    }
    if (read_errs) {
        fprintf(stderr, "read/check %d of %d failed.\n", read_errs, nr_reads);
        return 1;
    }
    return 0;
}

/**
 * Only for my concerned chip: Samsung 1GiB 3.3v
 */
static int scan_badblocks(void)
{
    int bb_cnt = 0;
    int err;

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
                    printf("bad blocks: %d", i);
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
                bbt[i] = true;
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
    loff_t ofs;

    er.start = block * meminfo.erasesize;
    er.length = meminfo.erasesize;

    printf("erasing block %d\n", block);
    if (ioctl(fd, MEMERASE, &er)) {
        perror("MEMERASE");
        if (markbad) {
            printf("mark bad block %d\n", block);
            ofs = er.start;
            if (ioctl(fd, MEMSETBADBLOCK, &ofs))
                perror("MEMSETBADBLOCK");
        }
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
        goto fail;
    } else if (n < len) {
        fprintf(stderr, "write error on pages [%d, %d]. len %ld actual %ld\n"
                , page_start, page_end, sizeof(buf), n);
        goto fail;
    }

    free(buf);
    return 0;

fail:
    free(buf);
    return -1;
}

static int scratch_block(int block)
{
    int page_start = block * (meminfo.erasesize / meminfo.writesize);
    int page_end = page_start + (meminfo.erasesize / meminfo.writesize) - 1;

    random_tree_walk_with_intvl(page_start, page_end, aligned_write
            , (void *)(long int)seeds[block]);
    random_tree_walk_with_intvl(page_start, page_end, aligned_read_and_compare
            , (void *)(long int)seeds[block]);
    return 0;
}

static int test_block(int block, void *nouse)
{
    UNUSED(nouse);

    if (bbt[block])
        printf("skip bad block %d\n", block);
    else if (! erase_block(block))
        scratch_block(block);
    return 0;
}

/*
 * Main program
 */
int main(int argc, char **argv)
{
    int i;
    unsigned char *wbuf, *rbuf, *kbuf;
    int pass;
    int nr_passes = 1;
    int keep_contents = 0;
    uint32_t offset = 0;
    uint32_t length = -1;
    int error = 0;

    for (;;) {
        static const char short_options[] = "hkl:mo:p:r:VS";
        static const struct option long_options[] = {
            { "help", no_argument, 0, 'h' },
            { "version", no_argument, 0, 'V' },
            { "markbad", no_argument, 0, 'm' },
            { "passes", required_argument, 0, 'p' },
            { "offset", required_argument, 0, 'o' },
            { "length", required_argument, 0, 'l' },
            { "reads", required_argument, 0, 'r' },
            { "keep", no_argument, 0, 'k' },
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

        case 'k':
            keep_contents = 1;
            break;

        case 'p':
            nr_passes = atol(optarg);
            break;

        case 'r':
            nr_reads = atol(optarg);
            break;

        case 'o':
            offset = simple_strtoul(optarg, &error);
            break;

        case 'l':
            length = simple_strtoul(optarg, &error);
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

    if (length == -1)
        length = meminfo.size;

    if (offset % meminfo.erasesize) {
        fprintf(stderr, "Offset %x not multiple of erase size %x\n",
            offset, meminfo.erasesize);
        exit(1);
    }
    if (length % meminfo.erasesize) {
        fprintf(stderr, "Length %x not multiple of erase size %x\n",
            length, meminfo.erasesize);
        exit(1);
    }
    if (length + offset > meminfo.size) {
        fprintf(stderr, "Length %x + offset %x exceeds device size %x\n",
            length, offset, meminfo.size);
        exit(1);
    }

    if (ioctl(fd, ECCGETSTATS, &oldstats)) {
        perror("ECCGETSTATS");
        close(fd);
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

    if (! (bbt = (bool *)malloc(mtd.eb_cnt))) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    memset(bbt, 0, mtd.eb_cnt);

    printf("memory: type %u flags 0x%x size %u erasesize %u writesize %u oobsize %u\n",
            meminfo.type, meminfo.flags, meminfo.size, meminfo.erasesize,
            meminfo.writesize, meminfo.oobsize); 
    printf("mtd: size %lld eb_cnt %d eb_size %d min_io_size %d"
            " subpage_size %d oob_size %d bb_allowed %d\n",
            mtd.size, mtd.eb_cnt, mtd.eb_size, mtd.min_io_size,
            mtd.subpage_size, mtd.oob_size, mtd.bb_allowed);
    printf("oob: useecc %d eccbytes %u\n", oobinfo.useecc, oobinfo.eccbytes);
    printf("ecc: corrections %d failures %d bad blocks %d bbt blocks %d\n",
            oldstats.corrected, oldstats.failed, oldstats.badblocks,
            oldstats.bbtblocks);

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

    printf("scanning bad blocks from oob\n");
    if (scan_badblocks()) {
        fprintf(stderr, "bad blocks info mismatched between kernel and oob\n");
        exit(1);
    }

    if (info_only) return 0;

    wbuf = malloc(meminfo.erasesize * 3);
    if (!wbuf) {
        fprintf(stderr, "Could not allocate %d bytes for buffer\n",
            meminfo.erasesize * 2);
        exit(1);
    }
    rbuf = wbuf + meminfo.erasesize;
    kbuf = rbuf + meminfo.erasesize;

    if (! (seeds = malloc(mtd.eb_cnt * sizeof(int)))) {
        fprintf(stderr, "out of memory in allocating seeds series\n");
        exit(1);
    }

    int *p = seeds;
    srand(time(NULL));
    for (int i = 0; i < mtd.eb_cnt; i++) *p++ = rand();

    srandom(time(NULL));
    return random_tree_walk(0, mtd.eb_cnt - 1, test_block, NULL);

    for (pass = 0; pass < nr_passes; pass++) {
        loff_t test_ofs;

        for (test_ofs = offset; test_ofs < offset+length; test_ofs += meminfo.erasesize) {
            ssize_t len;

            srand(time(NULL));

            if (ioctl(fd, MEMGETBADBLOCK, &test_ofs)) {
                printf("\rBad block at 0x%08x\n", (unsigned)test_ofs);
                continue;
            }

            for (i=0; i<meminfo.erasesize; i++)
                wbuf[i] = rand();

            if (keep_contents) {
                printf("\r%08x: reading... ", (unsigned)test_ofs);
                fflush(stdout);

                len = pread(fd, kbuf, meminfo.erasesize, test_ofs);
                if (len < meminfo.erasesize) {
                    printf("\n");
                    if (len)
                        fprintf(stderr, "Short read (%zd bytes)\n", len);
                    else
                        perror("read");
                    exit(1);
                }
            }
            if (erase_and_write(test_ofs, wbuf, rbuf, nr_reads))
                continue;
            if (keep_contents)
                erase_and_write(test_ofs, kbuf, rbuf, 1);
        }
        printf("\nFinished pass %d successfully\n", pass+1);
    }
    /* Return happy */
    return 0;
}
