/*
 *     ,  ,
 *    (\ "\
 *    ,--;.)._
 *   ).,-._ . ""-,_
 *  /.'".- " 8 o . ";_
 *  `L_ ,-)) o . 8.o .""-.---...,,--------.._   _"";
 *   """  ")) 8 . . 8 . 8   8  8  8  8. 8 8 ._""._;
 *         ";. .8 .8  .8  8  8  8  8 . 8. 8 .".""
 *            ;.. 8 ; .  8. 8  8  8 . } 8 . 8 :
 *             ;.. 8 ; 8. 8  8  8  8 (  . 8 . :
 *               ;. 8 \ .   .......;;;  8 . 8 :
 *                ;o  ;"\\\\```````( o(  8   .;
 *                : o:  ;           :. : . 8 (
 *                :o ; ;             "; ";. o :
 *                ; o; ;               "; ;";..\
 *                ;.; .:                )./  ;. ;
 *               _).< .;              _;./  _;./
 *             ;"__/--"             ((__7  ((_J
 *
 *	tfcrypt toolkit -- a set of tools to manipulate data.
 *
 *	tfcrypt contains Threefish block cipher, Skein hash function,
 *	secure key derivation function built on them.
 *	It is very accurate about IO, and includes error handling code.
 *
 *	It also embeds a variable bit hashsum sksum tool akin md5sum.
 *
 *	It contains base64 encoder/decoder to ease transmission of
 *	encrypted data over ascii networks, such as social networks
 *	like Facebook, Twitter and VK.
 *
 *	It helps to identify data tampering with embedded MAC signature.
 *	It's encryption part runs in CTR mode.
 *	It also supports TCTR and CBC modes.
 *
 *	It includes a handy benchmark tool.
 *
 *	And it's a pure Unix tool which does IO not only with files,
 *	but (to reasonable amount) with data streams like pipes.
 *
 *	Please see README file that is shipped with source code.
 *
 *	tfcrypt is not copyrighted and does not require a notice of
 *	original authorship to be included everywhere.
 *	Threefish and Skein code is by Bruce Schneier et.al.,
 *	which is also was placed into public domain.
 *
 *	This code is placed into public domain.
 */

/* Some evil FTM stuff. Heck I hate it. */
#ifndef _BSD_SOURCE
#define _BSD_SOURCE
#endif
#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE 700
#endif
#ifndef _LARGEFILE64_SOURCE
#define _LARGEFILE64_SOURCE
#endif

#ifndef _TFCRYPT_VERSION
#error Version number may help you to identify missing functionality.
#endif

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <libgen.h>
#include <stdarg.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <limits.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/time.h>

#include <stdint.h>
#include "tfcrypt.h"
#include "getpasswd.h"

#include "defs.h"

static char *progname;
static int exitcode;

static unsigned char xtweak[sizeof(tweak)];
static int macbits = TF_MAX_BITS;

static char *randsource = DEFAULT_RANDSOURCE;
static unsigned long long iseek_blocks, iseek, oseek, maxlen = ULL_1;
static unsigned long long total_processed_src, total_processed_dst;
static unsigned long long delta_processed;
static unsigned long long genrandom_nr_bytes, genzero_nr_bytes;
static TF_X(ctx) tctx;
static SK_X(ctx) sctx;
static int sfd, kfd = -1, dfd = 1;
static struct stat s_stat;
static unsigned char srcblk[BLKSIZE], dstblk[BLKSIZE], *pblk = dstblk;
static unsigned char key[TF_KEY_SIZE], counter[TF_KEY_SIZE];
static char pwdask[256], pwdagain[256];
static char tmp_data[TF_BLOCK_SIZE * 2];

static size_t lio, lrem, ldone, lblock, maxkeylen = SIZET_1, ctrsz = TF_BLOCK_SIZE;

static struct sigaction sa;

static int do_edcrypt = DO_ENCRYPT, do_stop, quiet, error_action;
static int do_mac, do_base64, do_raw;
static int counter_opt, rawkey, mackey_opt;
static int x, c, password, overwrite_source, idx, write_flags, do_fsync, do_pad;
static int do_preserve_time, do_stats_in_gibs, do_statline_dynamic = YES, do_less_stats;
static char *srcfname = STDIN_NAME, *dstfname = STDOUT_NAME, *do_mac_file, *counter_file;
static char *genkeyf, *tweakf, *mackeyf;
static int verbose;
static long status_timer, do_benchmark;

static unsigned long long current_time, delta_time;

static char *stoi;

static struct getpasswd_state getps;

static void xexit(int status)
{
	memset(key, 0, sizeof(key));
	memset(counter, 0, sizeof(counter));
	memset(&getps, 0, sizeof(struct getpasswd_state));
	memset(pwdask, 0, sizeof(pwdask));
	memset(pwdagain, 0, sizeof(pwdagain));
	memset(tmp_data, 0, sizeof(tmp_data));
	memset(&sctx, 0, sizeof(SK_X(ctx)));
	if (ctr_mode == MODE_TCTR) TFC_X(done)(&tctx.tfc);
	else TF_X(done)(&tctx);
	memset(&tctx, 0, sizeof(TF_X(ctx)));
	memset(srcblk, 0, sizeof(srcblk));
	memset(dstblk, 0, sizeof(dstblk));
	exit(status);
}

static inline void tf_udelay(unsigned long long useconds)
{
	usleep((useconds_t)useconds);
}

static void tf_vfsay(FILE *where, int addnl, unsigned long long us, const char *fmt, va_list ap)
{
	if (us) fputs("\033[2K\r", where); /* VT100 compatible */
	if (!strcmp(fmt, "\n")) {
		fputc('\n', where);
		return;
	}

	vfprintf(where, fmt, ap);
	if (addnl) fputc('\n', where);
	fflush(where);

	if (us) tf_udelay(us);
}

static void tf_nfsay(FILE *where, const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	tf_vfsay(where, NO, 0, fmt, ap);
	va_end(ap);
}

static void tf_esay(const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	tf_vfsay(stderr, YES, 0, fmt, ap);
	va_end(ap);
}

static void tf_say(const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	tf_vfsay(stdout, YES, 0, fmt, ap);
	va_end(ap);
}

static int getps_filter(struct getpasswd_state *getps, int chr, size_t pos)
{
	if (chr == '\x03') { /* ^C */
		getps->retn = (size_t)-1;
		return 6;
	}
	return 1;
}

static int isnum(const char *s)
{
	char *p;
	if (!s || *s == 0) return 0;
	strtol(s, &p, 10);
	return (*p == 0);
}

/*
 * Accept simple single char prefix names
 */
static unsigned long long xpstrtoull(const char *s, char **stoi)
{
	char pfx[2] = {0, 0};
	char N[128];
	size_t l;
	unsigned long long gbgib = 0, ret = 0;

	if (!s) return 0;

	xstrlcpy(N, s, sizeof(N));
	l = strnlen(N, sizeof(N));
	*pfx = *(N+l-1);
	if (!isnum(pfx)) *(N+l-1) = 0;

	*stoi = NULL;
	if (isnum(pfx) || *pfx == 'B' || *pfx == 'c') ret = strtoull(N, stoi, 10);
		/* if no prefix, or prefix is B/c, then bytes */
	else if (*pfx == 'W') ret = strtoull(N, stoi, 10)*2; /* short int or old word */
	else if (*pfx == 'I') ret = strtoull(N, stoi, 10)*4; /* int or modern word */
	else if (*pfx == 'L') ret = strtoull(N, stoi, 10)*8; /* 64 bit word */
	else if (*pfx == 'e') ret = strtoull(N, stoi, 10)*TF_BLOCK_SIZE; /* current TF block size */
	else if (*pfx == 'E') ret = strtoull(N, stoi, 10)*BLKSIZE; /* defined IO block size */
	else if (*pfx == 'b' || *pfx == 's') ret = strtoull(N, stoi, 10)*512; /* 512 byte disk block */
	else if (*pfx == 'p' || *pfx == 'S') ret = strtoull(N, stoi, 10)*4096; /* page size, or AF disk block */
	else if (*pfx == 'k' || *pfx == 'K') {
		gbgib = do_stats_in_gibs == YES ? 1000 : 1024;
	}
	else if (*pfx == 'm' || *pfx == 'M') {
		gbgib = do_stats_in_gibs == YES ? 1000 * 1000 : 1024 * 1024;
	}
	else if (*pfx == 'g' || *pfx == 'G') {
		gbgib = do_stats_in_gibs == YES ? 1000 * 1000 * 1000 : 1024 * 1024 * 1024;
	}
	else if (*pfx == 'T') {
		gbgib = do_stats_in_gibs == YES ? 1000000000000ULL : 1099511627776ULL;
	}
	else if (*pfx == 'P') {
		gbgib = do_stats_in_gibs == YES ? 1000000000000000ULL : 1125899906842624ULL;
	}
	else ret = strtoull(N, stoi, 10); /* oh, don't know, stoi for you */
	if (gbgib) ret = strtoull(N, stoi, 10) * gbgib;

	return ret;
}

static void usage(void)
{
	int is_embedded_prog = NO;

	if (optopt == 'V') {
		tf_say("tfcrypt toolkit (%u bits), version %s.",
			TFC_U(TF_MAX_BITS), _TFCRYPT_VERSION);
		xexit(0);
	}

	if ((strlen(progname) <= 9)
	&& ((!strcmp(progname, "sksum"))
	|| ((!memcmp(progname, "sk", 2))
	&& (!memcmp(progname+3, "sum", 3)
	|| !memcmp(progname+4, "sum", 3)
	|| !memcmp(progname+5, "sum", 3)
	|| !memcmp(progname+6, "sum", 3))))) {
		is_embedded_prog = YES;
		tf_say("usage: %s [-AW] [-l length] [-c <file>] [-U <file>] [source] ...", progname);
		tf_say("\n");
		tf_say("%s: calculate and print Skein hashsum of stream.", progname);
		tf_say("  -A: format checksum in base64 rather than in binary hex.");
		tf_say("  -W: output raw binary checksum and remove filename(s) from output.");
		tf_say("  -l length: read only these first bytes of source.");
		tf_say("  -c <file>: read hashes list from file and check them.");
		tf_say("  -U <file>: read Skein MAC key from file.");
		tf_say("sksum can also be invoked as skBITSsum, for example,");
		tf_say("sk256sum or sk512sum, where 256 or 512 or else is a");
		tf_say("bits setting usually set with -b option (disabled here).");
		tf_say("multiple sources can be given in cmdline, and if one of");
		tf_say("them is specified as \"-\", then reads are performed from stdin.");
		tf_say("\n");
	}
	else if (!strcmp(progname, "base64")) {
		is_embedded_prog = YES;
		tf_say("usage: %s [-ed] [source] [output]", progname);
		tf_say("\n");
		tf_say("tfcrypt embedded base64 encoder/decoder.");
		tf_say("  -e: encode stream into base64.");
		tf_say("  -d: decode base64 stream.");
		tf_say("no error checking is performed.");
		tf_say("\n");
	}
	else if (!strcmp(progname, "tfsign")) {
		is_embedded_prog = YES;
		tf_say("usage: %s [TFCopts] reffile/size [keyfile] [hashfile] [outsig]", progname);
		tf_say("\n");
		tf_say("%s: generate valid encrypted MAC signature for already encrypted stream.", progname);
		tf_say("  TFCopts are tfcrypt options. You may use any option to adjust internals.");
		tf_say("  keyfile is a key with which a stream itself was encrypted.");
		tf_say("  hashfile is a precalculated hashsum which must be encrypted,");
		tf_say("  and used as a MAC verification signature.");
		tf_say("  reffile is reference file or device to stat it's size.");
		tf_say("  It is needed to calculate exact number of TF blocks to seek.");
		tf_say("  %s will never write to this file.", progname);
		tf_say("  Instead of specifying reffile you may specify a size in bytes (with prefixes),");
		tf_say("  if you (for some reason) do not wish to provide a real file just to stat it's size.");
		tf_say("  It simply may be not there: absent, sent or too big to be there.");
		tf_say("  If last block will not round to %u bytes, CTR value will be incremented by one TF block.", TFC_U(TF_BLOCK_SIZE));
		tf_say("\n");
		tf_say("To attach a binary signature file to encrypted stream: join them with");
		tf_say("concatenation like Unix cat: \"cat crypt.file crypt.sig >scrypt.out\",");
		tf_say("or simply append signature: \"cat crypt.sig >>crypt.file\".");
		tf_say("\n");
		tf_say("WARNING: This is a *hacky* embedded program, and you should not normally use it!");
		tf_say("\n");
	}

	if (is_embedded_prog) {
		tf_say("This program is physical part of tfcrypt toolkit.");
		tf_say("(see it's version with %s -V)", progname);
		tf_say("Please note that other tfcrypt options are either ignored there,");
		tf_say("or result of using them is undefined and it's not a bug.");
		xexit(1);
	}

	tf_say("usage: %s [opts] [--] [key] [source] [output]", progname);
	tf_say("\n");
	tf_say("tfcrypt toolkit: encrypt streams with Threefish in CTR mode,");
	tf_say("calculate and check Skein hashsums, generate CSPRNG quality random data,");
	tf_say("convert encrypted data into ASCII format to ease transmission.");
	tf_say("\n");
	tf_say("  -e, -d: encrypt, decrypt (it maybe required).");
	tf_say("  -p: instead of using key, ask for password.");
	tf_say("  -k: use raw (%u byte) key instead of deriving it from arbitrary data.", TFC_U(TF_KEY_SIZE));
	tf_say("  -K <file>: generate key from keyfile or password and write it to file.");
	tf_say("  -w: overwrite source file. If not file, ignored.");
	tf_say("  -b BITS: number of bits of key (from 8 to %u, default is %u).", TFC_U(TF_MAX_BITS), TFC_U(TF_MAX_BITS));
	tf_say("  -n PASSES: number of passes to perform in skein function.");
	tf_say("    Default is always defined when building tfcrypt.");
	tf_say("  -t <file>: read tweak from file and use it instead of embedded one.");
	tf_say("  -T: randomise tweak value based on rawkey hash (can be default).");
	tf_say("  -C mode: mode of operation: CTR, TCTR or CBC.");
	tf_say("    CTR encrypts an incrementing counter, then adds plaintext to result.");
	tf_say("    TCTR mode is like CTR mode, but has CBC like properties.");
	tf_say("    TCTR mode is more secure: it does not require random counter,");
	tf_say("    and CBC like property gives ability to completely hide changes, unlike CTR.");
	tf_say("    TCTR mode is specific to tfcrypt and it is not portable.");
	tf_say("    CBC mode is well known and old one. Included for testing.");
	tf_say("    Historically, tfcrypt default mode is CTR.");
	tf_say("    Default encryption mode can be changed when building tfcrypt.");
	tf_say("  -c opt: initial CTR value initialisation mode:");
	tf_say("    show: do default action, then dump CTR value to stderr,");
	tf_say("    head: when decrypting, read CTR from beginning of stream,");
	tf_say("    rand: generate random CTR and write it to beginning of stream,");
	tf_say("    <file>: read CTR from given file (both when encrypting/decrypting).");
	tf_say("      default is to derive CTR from user provided password or keyfile with");
	tf_say("      a single sk%u function turn over derived, %u byte raw key", TFC_U(TF_MAX_BITS), TFC_U(TF_KEY_SIZE));
	tf_say("  -q: always be quiet, never tell anything (except when signaled).");
	tf_say("  -v: print number of read and written encrypted bytes, and explain stages.");
	tf_say("  -V seconds: activate timer that will repeatedly print statistics to stderr.");
	tf_say("  -a: shortcut of -O xtime.");
	tf_say("  -B seconds: do an in-memory random data benchmark of Threefish.");
	tf_say("  -r <file>: specify random source instead of /dev/urandom.");
	tf_say("  -R nr_bytes: generate nr_bytes of random bytes suitable for use as key data.");
	tf_say("    -R also supports these aliases specified instead of nr_bytes:");
	tf_say("    bits: output this number of bits of random data, converted to bytes,");
	tf_say("    cbs: output fixed maximum crypt block/key size (%u bytes),", TFC_U(TF_BLOCK_SIZE));
	tf_say("    iobs: output %s builtin block size BLKSIZE (%u bytes),", progname, TFC_U(BLKSIZE));
	tf_say("    if nr_bytes is not a valid number or alias, this string will be");
	tf_say("    used to attempt to open it as file, and examine it's size.");
	tf_say("    Then this examined size will be set as nr_bytes to output.");
	tf_say("  -Z nr_bytes: like -R, but emit zero stream instead of random.");
	tf_say("  -D MACBITS: like -b, but affects Skein MAC separately.");
	tf_say("  -U key/pwd/<file>: read Skein MAC key from file.");
	tf_say("    key: use primary encryption rawkey as a MAC key.");
	tf_say("    pwd: ask for password string that will be used as MAC key.");
	tf_say("  -S MAC: append MAC signature to end of file:");
	tf_say("    MAC: embed MAC signature into file itself at the end,");
	tf_say("    <file>: write a detached MAC signature into separate <file>,");
	tf_say("    -: write a detached MAC signature to stdout.");
	tf_say("    useful only with variable length files! For block devices,");
	tf_say("    specify a separate file name to save signature to: -S file.");
	tf_say("  -A: format raw binary data, like MAC signature or sksum hash, in base64.");
	tf_say("  -W: output pure binary data, and disable any strings addition in sksum.");
	tf_say("  -M MAC: verify attached MAC signature when decrypting a file:");
	tf_say("    MAC: embed MAC signature into file itself at the end,");
	tf_say("    <file>: write a detached MAC signature into separate <file>,");
	tf_say("    -: read a detached MAC signature from stdin,");
	tf_say("    drop: do not verify attached MAC, if any, and drop it from output.");
	tf_say("    useful only with variable length files! For block devices,");
	tf_say("    specify a separate file name to read signature from: -M file.");
	tf_say("  -m: just verify MAC provided with -M. Do not write output file.");
	tf_say("    This option must be specified after -M.");
	tf_say("  -E how: how to behave on I/O errors (both src or dst):");
	tf_say("    exit: print error if not quiet, then exit,");
	tf_say("    cont: print error if not quiet, then continue,");
	tf_say("      no action to pad missing data is attempted.");
	tf_say("      may be dangerous when working with block devices.");
	tf_say("    sync: print error if not quiet, then continue.");
	tf_say("      pad missing data block with zeroes.");
	tf_say("      note that sync works only with read errors!");
	tf_say("  default error action is exit with printing status if not quiet.");
	tf_say("  -O opts: set options (comma separated list):");
	tf_say("    sync: request a synchronous I/O for a output,");
	tf_say("    fsync: on each write() call a corresponding fsync(fd),");
	tf_say("    trunc: open(O_WRONLY) will truncate output file to zero size.");
	tf_say("    pad: pad incomplete (l.t. %u bytes) block with zeroes.", TFC_U(TF_BLOCK_SIZE));
	tf_say("    xtime: copy timestamps from source to destination files.");
	tf_say("    gibsize: use SI units of size: 1k = 1000. Applies only to size prefixes.");
	tf_say("    Computers convention is to use 1024, whereas SI/hdd measure in 1000.");
	tf_say("    pstat: force status line to be plain: no fancy dynamic stuff.");
	tf_say("    Dynamic line works well only on VT100 compatible ttys, and");
	tf_say("    when the whole status line width is smaller than tty width.");
	tf_say("    statless: emit less information in status line (only processed data).");
	tf_say("    iseek=val: seek source file/device by these val bytes.");
	tf_say("    Initial counter is adjusted automatically.");
	tf_say("    ixseek=val: rawseek source file/device by these val bytes.");
	tf_say("    Do not adjust initial counter automatically.");
	tf_say("    ictr=val: Increment initial counter by this val blocks.");
	tf_say("    The size of each block is %u bytes.", TFC_U(TF_BLOCK_SIZE));
	tf_say("    ictr option is valid only for CTR and CTR like modes.");
	tf_say("    ixctr=val: Increment initial counter by this val bytes.");
	tf_say("    Internally this number is translated into number of %u byte blocks.",
								TFC_U(TF_BLOCK_SIZE));
	tf_say("    oseek=val: seek destination file/device by these val bytes.");
	tf_say("    count=val: process only these val bytes, both input and output.");
	tf_say("    xkey=val: take only val bytes from user keyfile.");
	tf_say("  -P: plain IO mode: disable encryption/decryption code at all.");
	tf_say("  -sum[HASHLEN]: hashsum a file using skein%u() and output HASHLEN hash.", TFC_U(TF_MAX_BITS));
	tf_say("  -b64 [source] [dest]: encode data in base64, optionally to files.");
	tf_say("  To specify -E with -sum, use: -E opt -- -sum[HASHLEN].");
	tf_say("\n");
	tf_say("Default is to ask for password, then encrypt stdin into stdout.");
	tf_say("Some cmdline parameters may be mutually exclusive, or they can");
	tf_say("generate errors or behave abnormally. Please understand that some");
	tf_say("dumb mode error checking may be not performed well, and please read");
	tf_say("the README included within package and this help text carefully.");
	tf_say("\n");
	xexit(1);
}

static void xerror(int noexit, int noerrno, int nostats, const char *fmt, ...)
{
	va_list ap;
	char *s;

	if (quiet) goto _ex;

	va_start(ap, fmt);

	tf_nfsay(stderr, "%s: ", progname);
	tf_vfsay(stderr, NO, 0, fmt, ap);
	if (errno && !noerrno) {
		s = strerror(errno);
		tf_esay(": %s", s);
	}
	else tf_esay("\n");

	va_end(ap);

	if (!nostats) print_crypt_status(0); /* forcibly print statistics, they can help... */

_ex:
	if (noexit) {
		errno = 0;
		return;
	}

	xexit(2);
}

static inline void xclose(int fd)
{
	if (close(fd) == -1)
		xerror(YES, NO, NO, "close(%d)", fd);
}

static void setup_next_alarm(unsigned useconds)
{
	struct itimerval it;

	memset(&it, 0, sizeof(struct itimerval));
	it.it_value.tv_sec = useconds / 1000000;
	it.it_value.tv_usec = useconds % 1000000;
	setitimer(ITIMER_REAL, &it, NULL);
}

static void describescale(unsigned long long num, double *w, int *scale)
{
	unsigned long long gbgib = (do_stats_in_gibs == YES) ? 1000 : 1024;

	if (num <= gbgib) {
		*w = num;
		*scale = 0;
	} /* B */
	else if ((num > gbgib)
		&& (num <= gbgib * gbgib)) {
		*w = (double)num / gbgib;
		*scale = 1;
	} /* K */
	else if ((num > gbgib * gbgib)
		&& (num <= gbgib * gbgib * gbgib)) {
		*w = (double)num / (gbgib * gbgib);
		*scale = 2;
	} /* M */
	else if ((num > gbgib * gbgib * gbgib)
		&& (num <= gbgib * gbgib * gbgib * gbgib)) {
		*w = (double)num / (gbgib * gbgib * gbgib);
		*scale = 3;
	} /* G */
	else if ((num > gbgib * gbgib * gbgib * gbgib)
		&& num <= gbgib * gbgib * gbgib * gbgib * gbgib) {
		*w = (double)num/ (gbgib * gbgib * gbgib * gbgib);
		*scale = 4;
	} /* T */
	else {
		*w = (double)num / (gbgib * gbgib * gbgib * gbgib * gbgib);
		*scale = 5;
	} /* P */
}

static void getcurtime(unsigned long long *tx)
{
	struct timeval t;
	memset(&t, 0, sizeof(t));

	gettimeofday(&t, NULL);
	*tx = t.tv_sec * 1000000 + t.tv_usec;

	memset(&t, 0, sizeof(t));
}

static off_t fdsize(int fd)
{
	off_t l, cur;

	cur = lseek(fd, 0L, SEEK_CUR);
	l = lseek(fd, 0L, SEEK_SET);
	if (l == -1) return -1;
	l = lseek(fd, 0L, SEEK_END);
	if (l == -1) return -1;
	lseek(fd, cur, SEEK_SET);
	return l;
}

static unsigned long long fnamesize(const char *fname, int noexit)
{
	int fnmfd;
	unsigned long long ret;

	fnmfd = open(fname, O_RDONLY);
	if (fnmfd == -1) {
		xerror(noexit, NO, YES, fname);
		return ULL_1;
	}
	ret = (unsigned long long)fdsize(fnmfd);
	if (ret == ULL_1) {
		xerror(noexit, NO, YES, "%s: not a seekable file", fname);
		return ret;
	}
	xclose(fnmfd);

	return ret;
}

static void fcopy_matime(int fd, const struct stat *st)
{
	struct timeval times[2];

	times[1].tv_sec = times[0].tv_sec = st->st_mtime;
	times[1].tv_usec = times[0].tv_usec = 0;
	if (futimes(fd, times) == -1) xerror(YES, NO, YES, "futimes(%d)", fd);
}

static inline size_t BLK_LEN_ADJ(unsigned long long filelen,
	unsigned long long read_already, size_t blklen)
{
	if (filelen == ULL_1) return blklen;
	return ((filelen - read_already) >= blklen) ? blklen : (filelen - read_already);
}

static void print_crypt_status(int signal)
{
	unsigned long long wr_speed;
	double seconds, human_totalproc_src, human_totalproc_dst, human_wr_speed;
	int src_scale_idx, dst_scale_idx, wr_speed_scale;
	const char *oper_mode, *inplace;
	static int last;

	/* signals delivered after FS/IO layer done it's job but too late. They're useless. */
	if (last == YES) return;
	/* main TF IO is done, no stats after that point should be emitted. */
	if (signal == 0) last = YES;

	switch (do_edcrypt) {
		case DO_ENCRYPT: oper_mode = "encrypted"; break;
		case DO_DECRYPT: oper_mode = "decrypted"; break;
		default: oper_mode = "written"; break;
	}

	if (signal == SIGINT && do_statline_dynamic == NO) tf_esay("\n");

	if (signal == SIGINT || signal == SIGTERM) {
		do_stop = STOP_FULL;
		total_processed_dst += sizeof(dstblk);
		delta_processed += sizeof(dstblk);
		status_timer = 0;
		verbose = NO;
	}

	getcurtime(&current_time);
	seconds = (current_time - delta_time) / 1000000.0;
	wr_speed = delta_processed / seconds;
	describescale(total_processed_src, &human_totalproc_src, &src_scale_idx);
	describescale(total_processed_dst, &human_totalproc_dst, &dst_scale_idx);
	describescale(wr_speed, &human_wr_speed, &wr_speed_scale);

	if (do_benchmark) {
		tf_say("done!");
		tf_say("%s benchmark results:", progname);
		tf_nfsay(stdout, "processed %llu (%.2f%s) bytes, "
			"avg. speed %llu (%.2f%s) B/s, time %lu us.",
			total_processed_src, human_totalproc_src, size_scale[src_scale_idx],
			wr_speed, human_wr_speed, size_scale[wr_speed_scale],
			(unsigned long)(current_time - delta_time));
		if (signal != SIGINT) tf_esay("\n");
		xexit(0);
	}

	if (do_statline_dynamic == YES) inplace = "\033[2K\r"; /* VT100 compatible */
	else inplace = "";

	if (do_less_stats == YES) {
		tf_nfsay(stderr, "%s%s:"
			" %s %.2f%s,"
			" %.2f%s B/s",
			inplace, progname,
			oper_mode,
			human_totalproc_dst, size_scale[dst_scale_idx],
			human_wr_speed, size_scale[wr_speed_scale]);
	}
	else {
		tf_nfsay(stderr, "%s%s: read: %llu (%.2f%s),"
			" %s %llu (%.2f%s) bytes,"
			" (%llu (%.2f%s) B/s)",
			inplace, progname,
			total_processed_src, human_totalproc_src, size_scale[src_scale_idx],
			oper_mode,
			total_processed_dst, human_totalproc_dst, size_scale[dst_scale_idx],
			wr_speed, human_wr_speed, size_scale[wr_speed_scale]);
	}
	/* newline is already emitted when ^C */
	if (signal != SIGINT && do_statline_dynamic == NO) tf_esay("\n");
	/* emit last newline if dynamic overwriting string */
	if (do_statline_dynamic == YES && signal == 0) tf_esay("\n");

	delta_processed = 0;
	getcurtime(&delta_time);

	if (signal == SIGTSTP) {
		tf_esay("stopping.");
		kill(getpid(), SIGSTOP);
	}

	if (status_timer) setup_next_alarm(status_timer);
}

static void change_status_width(int signal)
{
	if (do_less_stats == YES) do_less_stats = NO;
	else if (do_less_stats == NO) do_less_stats = YES;
}

static void change_status_timer(int signal)
{
	static unsigned long long reset_timer;
	unsigned long long t;

	getcurtime(&t);
	if (reset_timer && (t - reset_timer) < DTOUSECS(0.1)) status_timer = 0;
	reset_timer = t;

	if (status_timer == 0) status_timer = DTOUSECS(0.25);
	else status_timer *= 2;

	if (verbose) tf_esay("status timer was changed to %.2fs", status_timer / 1000000.0);
	setup_next_alarm(status_timer);
}

static int skeinfd(int fd, unsigned long long readto, sk1024_ctx *keyctx, unsigned char *hash, int bits)
{
	size_t xi, xr, xb, xd;
	int st = NO;
	unsigned long long total = 0;
	unsigned char blk[BLKSIZE], *sblk;
	unsigned char dgst[TF_KEY_SIZE];
	off_t l = 0;
	SK_X(ctx) ctx;

	if (fd == -1) goto _fail;
	if (fd > 2) {
		/* get file size if fd is pretends to be a file */
		l = fdsize(fd);
		if (l == -1) goto _fail;
	}

	memset(&ctx, 0, sizeof(SK_X(ctx)));
	if (keyctx) memcpy(ctx.tfc.K, keyctx->tfc.K, sizeof(ctx.tfc.K));
	SK_X(init)(&ctx, bits, keyctx ? YES : NO);

	errno = 0;
	while (1) {
		if (st) break;
		sblk = blk;
		xb = xr = BLK_LEN_ADJ(readto, total, sizeof(blk));
		xd = 0;
_again:		xi = read(fd, sblk, xr);
		if (xi == 0) st = YES;
		if (xi != SIZET_1) xd += xi;
		if (errno) {
			switch (error_action) {
				case ERRACT_CONT: goto _again; break;
				case ERRACT_SYNC:
					xi = xr = xd = xb;
					total += xi;
					memset(blk, 0, xi);
					break;
				default: goto _fail; break;
			}
		}
		if (xi && xi < xr) {
			sblk += xi;
			xr -= xi;
			goto _again;
		}
		total += xd;
		SK_X(update)(&ctx, blk, xd);
		if (readto != ULL_1 && total >= readto) break;
	}

	if (fd > 2) lseek(fd, l, SEEK_SET);

	SK_X(final)(&ctx, dgst);
	memset(&ctx, 0, sizeof(SK_X(ctx)));

	memset(blk, 0, BLKSIZE);
	memmove(hash, dgst, TF_FROM_BITS(bits));
	return YES;

_fail:
	memset(&ctx, 0, sizeof(SK_X(ctx)));
	memset(hash, 0, TF_FROM_BITS(bits));
	return NO;
}

static void skein_loop(const unsigned char *src, size_t len, unsigned char *digest,
			unsigned int bits, unsigned int passes)
{
	unsigned char dgst[TF_KEY_SIZE] = {0};
	int x;

	if (passes == 0)
		return;

	skeinX(src, len, dgst, bits);
	for (x = 0; x < passes-1; x++)
		skeinX(dgst, TF_FROM_BITS(bits), dgst, bits);

	memmove(digest, dgst, TF_FROM_BITS(bits));
}

static inline void binhex(FILE *where, const unsigned char *p, size_t n, int nl)
{
	size_t x;
	for (x = 0; x < n; x++) tf_nfsay(where, "%02hx", (unsigned char)p[x]);
	if (nl) tf_nfsay(where, "\n");
}

static inline void binb64(FILE *where, const unsigned char *p, size_t n, int nl)
{
	struct base64_encodestate estate;
	memset(&estate, 0, sizeof(struct base64_encodestate));
	base64_eprint(where, &estate, (const char *)p, n);
	if (nl) tf_nfsay(where, "\n");
}

static void tfcrypt_getrandom(void *buf, size_t size)
{
	char *ubuf = buf;
	int fd = -1;
	size_t sz = size, rd;

	/* Most common and probably available on every Nix, */
	fd = open(randsource, O_RDONLY);
	/* OpenBSD arc4 */
	if (fd == -1) fd = open("/dev/arandom", O_RDONLY);
	/* OpenBSD simple urandom */
	if (fd == -1) fd = open("/dev/prandom", O_RDONLY);
	/* OpenBSD srandom, blocking! */
	if (fd == -1) fd = open("/dev/srandom", O_RDONLY);
	/* Most common blocking. */
	if (fd == -1) fd = open("/dev/random", O_RDONLY);
	/* Very bad, is this a crippled chroot? */
	if (fd == -1) xerror(NO, YES, YES, "random source is required (tried %s)", randsource);

_again:	rd = read(fd, ubuf, sz);
	/* I want full random block, and there is no EOF can be! */
	if (rd < sz && rd != SIZET_1) {
		if (verbose && ubuf == buf)
			tf_esay("%s: generating %zu random bytes, this may take time ...",
				randsource, size);

		ubuf += rd;
		sz -= rd;

		if (verbose) tf_esay("%s: got %zu bytes, waiting for remaining %zu bytes ...",
				randsource, rd, sz);

		goto _again;
	}

	xclose(fd);

	if (verbose && ubuf != buf) tf_esay("%s: all %zu bytes are here!", randsource, size);

	/* regenerate (P)RNG into Skein PRNG. */
	skeinX(buf, size, buf, TF_TO_BITS(size));
}

static void char_to_nul(char *s, size_t l, int c)
{
	while (*s && l) { if (*s == c) { *s = 0; break; } s++; l--; }
}

/* what an abusive declaration fgets has */
static int xfgets(char *s, size_t n, FILE *f)
{
	/* safety first! */
	memset(s, 0, n);

	if (fgets(s, (int)n, f) == s) {
		char_to_nul(s, n, '\n');
		return 1;
	}

	return 0;
}

static inline int isbase64(const char *s)
{
	while (*s) {
		if (*s >= 'g' && *s <= 'z') return 1;
		if (*s >= 'G' && *s <= 'Z') return 1;
		if (*s == '+' || *s == '/' || *s == '=') return 1;
		s++;
	}
	/*
	 * Found only hex digits.
	 * Technically still can be base64,
	 * but WILL NOT appear as a hash value,
	 * because of randomness.
	 */
	return 0;
}

static inline int chrbin(char x)
{
	if (x >= '0' && x <= '9')
		return x - '0';
	if (x >= 'A' && x <= 'F')
		return x - 'A' + 10;
	if (x >= 'a' && x <= 'f')
		return x - 'a' + 10;
	return 0;
}

static void hex2bin(const char *s, unsigned char *d)
{
	const char *S = s;
	int x = 0;

	while (*s) {
		if ((s-S) % 2) {
			x = (x << 4) ^ chrbin(*s);
			*d = x; d++;
		}
		else x = chrbin(*s);
		s++;
	}
}

static void do_sksum(char *spec, char **fargv, int b64out, int rawout)
{
	int fd = -1;
	int bits;
	unsigned char hash[TF_KEY_SIZE] = {0};
	int x = 0, xx;

	/* no bits specifier anywhere, just sum with TF_MAX_BITS. */
	if (!strcmp(spec, "sksum")) {
		bits = TF_MAX_BITS;
		goto _dothat;
	}

	if ((sscanf(spec, "sk%dsum", &bits) < 1)
	&&  (sscanf(spec, "-sum%d",  &bits) < 1))
		bits = TF_MAX_BITS;

	if (bits < 8 || bits > TF_MAX_BITS)
		xerror(NO, YES, YES,
		"%u: invalid bits number specified!\n"
		"tfcrypt supports from 8 to %u bits, divisible by 8.",
		bits, TFC_U(TF_MAX_BITS));

	if (!bits || bits % 8)
		xerror(NO, YES, YES,
		"%u: invalid bits number specified!\n"
		"Number of bits must start from 8 and be divisible by 8.",
		bits, TFC_U(TF_MAX_BITS));

_dothat:
	/* HACK! Reusing counter_file ptr here as per "-c" opt for checking. */
	if (counter_file) {
		FILE *f;
		char *s, *d;
		int failed = 0, totaltested = 0;

		/*
		 * Why I use stdio here? Because getting lines
		 * that way is a lot easier, and there are no
		 * any cryptosecrets are involved, so stay safe.
		 */
		if (!strcmp(counter_file, "-")) f = stdin;
		else f = fopen(counter_file, "r");
		if (!f) xerror(NO, NO, YES, counter_file);

		while (1) {
			memset(srcblk, 0, sizeof(srcblk));
			x = xfgets((char *)srcblk, sizeof(srcblk), f);
			if (x == 0) break;
			s = strchr((char *)srcblk, ' ');
			if (!s || *(s+1) != ' ') {
				xerror(YES, NO, YES, "invalid string %s", srcblk);
				exitcode = 2;
				continue;
			}
			*s = 0; *(s+1) = 0; d = s+2; s = (char *)srcblk;
			if (!*d || !strcmp(d, "-")) continue;
			fd = open(d, O_RDONLY | O_LARGEFILE);
			if (fd == -1) {
				xerror(YES, NO, YES, d);
				exitcode = 1;
				continue;
			}

			if (skeinfd(fd, maxlen, mackey_opt ? &sctx : NULL, hash, bits) != YES) {
				xerror(YES, NO, YES, "%s", d);
				exitcode = 1;
				continue;
			}
			xclose(fd);
			if (isbase64(s)) { /* base64 encoded hash */
				base64_decode(tmp_data, sizeof(tmp_data), s, strlen(s));
			}
			else { /* regular hex encoded hash */
				hex2bin(s, (unsigned char *)tmp_data);
			}

			if (!memcmp(hash, tmp_data, TF_FROM_BITS(bits))) {
				tf_say("%s: OK", d);
			}
			else {
				tf_say("%s: FAILED", d);
				failed++;
			}
			totaltested++;
		}

		fclose(f);
		if (failed) {
			if (totaltested > 1 && failed == totaltested)
				tf_esay("%s: WARNING: possible that %u bits value is invalid,",
					progname, bits);
				if (mackey_opt == NO)
					tf_esay("%s: or missing MAC keyfile or MAC password.", progname);
				else if (mackey_opt == MACKEY_PASSWD)
					tf_esay("%s: or MAC password is invalid.", progname);
				else if (mackey_opt == MACKEY_FILE)
					tf_esay("%s: or MAC keyfile is invalid.", progname);
				/* rawkey cannot be used here. */
			tf_esay("%s: WARNING: %u of %u computed checksums did NOT match",
				progname, failed, totaltested);
			exitcode = 1;
		}
		xexit(exitcode);
	}

	for (xx = 0; fargv[xx]; xx++);
	if (xx == 0) {
		fd = 0;
		goto _dohash;
	}

	for (x = 0; fargv[x] && xx; x++) {
		if (!strcmp(fargv[x], "-")) fd = 0;
		else fd = open(fargv[x], O_RDONLY | O_LARGEFILE);
		if (fd == -1) {
			xerror(YES, NO, YES, fargv[x]);
			exitcode = 1;
			continue;
		}

_dohash:
		/* if not specified, maxlen is already -1. */
		if (skeinfd(fd, maxlen, mackey_opt ? &sctx : NULL, hash, bits) != YES) {
			xerror(YES, NO, YES, "%s", fargv[x]);
			exitcode = 1;
			continue;
		}
		xclose(fd);
		if (b64out) binb64(stdout, hash, TF_FROM_BITS(bits), 0);
		else if (rawout) write(1/*stdout*/, hash, TF_FROM_BITS(bits));
		else binhex(stdout, hash, TF_FROM_BITS(bits), 0);
		if (rawout == NO) tf_say("  %s", fargv[x] ? fargv[x] : "-");
	}

	memset(hash, 0, sizeof(hash));
	xexit(exitcode);
}

static void do_edbase64(char *spec, char **fargv)
{
	struct base64_decodestate dstate;
	struct base64_encodestate estate;
	size_t lread = 0;

	sfd = 0; dfd = 1;

	if (fargv[0]) {
		if (!strcmp(fargv[0], "-")) sfd = 0;
		else {
			sfd = open(fargv[0], O_RDONLY | O_LARGEFILE);
			if (do_preserve_time) if (fstat(sfd, &s_stat) == -1)
				xerror(YES, NO, YES, "stat(%s)", fargv[0]);
		}
		if (sfd == -1) xerror(NO, NO, YES, fargv[x]);
	}

	if (fargv[0] && fargv[1]) {
		if (!strcmp(fargv[1], "-")) dfd = 1;
		else dfd = open(fargv[1], O_WRONLY | O_CREAT | O_LARGEFILE | write_flags, 0666);
		if (dfd == -1) xerror(NO, NO, YES, fargv[1]);
	}

	/* encode */
	if (do_edcrypt == DO_ENCRYPT) {
		memset(&estate, 0, sizeof(struct base64_encodestate));
		base64_init_encodestate(&estate);
	}
	/* decode */
	else if (do_edcrypt == DO_DECRYPT) {
		memset(&dstate, 0, sizeof(struct base64_decodestate));
		base64_init_decodestate(&dstate);
	}

	errno = 0;
	while (1) {
		if (do_stop) break;
		pblk = srcblk;
		lblock = lrem = do_edcrypt == DO_DECRYPT ? B64_DWIDTH : B64_EWIDTH;
		ldone = 0;
_again:		lio = read(sfd, pblk, lrem);
		if (lio == 0) do_stop = YES;
		if (lio != SIZET_1) ldone += lio;
		if (errno) {
			switch (error_action) {
				case ERRACT_CONT: xerror(YES, NO, NO, fargv[0]); break;
				case ERRACT_SYNC:
					xerror(YES, NO, NO, fargv[0]);
					lio = ldone = lrem = lblock;
					memset(srcblk, 0, lio);
					break;
				default: xerror(NO, NO, NO, fargv[0]); break;
			}
		}
		if (lio && lio < lrem) {
			pblk += lio;
			lrem -= lio;
			goto _again;
		}

		if (do_edcrypt == DO_ENCRYPT) {
			estate.count = 0;
			base64_encode_block((const char *)srcblk, ldone, (char *)dstblk, &estate);
			lread = ldone;
			ldone = estate.count;
		}
		else if (do_edcrypt == DO_DECRYPT) {
			dstate.count = 0;
			base64_decode_block((const char *)srcblk, ldone, (char *)dstblk, sizeof(dstblk), &dstate);
			ldone = dstate.count;
		}

		pblk = dstblk;
		if (ldone == 0) {
			do_stop = STOP_FULL;
			break;
		}
		lrem = ldone;
		ldone = 0;
_wagain:	lio = write(dfd, pblk, lrem);
		if (do_edcrypt == DO_ENCRYPT) {
			if (lread >= lblock || do_stop == STOP_FULL)
				lio += write(dfd, "\n", 1);
		}
		if (lio != SIZET_1) ldone += lio;
		if (errno) {
			switch (error_action) {
				case ERRACT_CONT: xerror(YES, NO, NO, fargv[1]); break;
				default: xerror(NO, NO, NO, fargv[1]); break;
			}
		}
		if (do_fsync) {
			errno = 0;
			fsync(dfd);
			if (errno) {
				switch (error_action) {
					case ERRACT_CONT: xerror(YES, NO, NO, fargv[1]); break;
					default: xerror(NO, NO, NO, fargv[1]); break;
				}
			}
		}
		if (lio < lrem) {
			pblk += lio;
			lrem -= lio;
			goto _wagain;
		}
	}

	if (do_edcrypt == DO_ENCRYPT && do_stop == STOP_BEGAN) {
		size_t t = estate.count;
		pblk = dstblk + estate.count;
		base64_encode_blockend((char *)dstblk, &estate);
		lrem = estate.count - t;
		ldone = 0;
		do_stop = STOP_FULL;
		goto _wagain;
	}

	memset(&estate, 0, sizeof(struct base64_encodestate));
	memset(&dstate, 0, sizeof(struct base64_decodestate));
	if (do_preserve_time) fcopy_matime(dfd, &s_stat);
	xexit(0);
}

static void do_benchmark_now(long useconds)
{
	for (x = 1; x < NSIG; x++) signal(x, SIG_IGN);
	memset(&sa, 0, sizeof(sa));
	sa.sa_flags = SA_RESTART;
	sa.sa_handler = print_crypt_status;
	sigaction(SIGINT, &sa, NULL);
	sigaction(SIGTERM, &sa, NULL);
	sigaction(SIGTSTP, &sa, NULL);
	sigaction(SIGALRM, &sa, NULL);
	setup_next_alarm(useconds);
	memset(&sa, 0, sizeof(sa));

	getcurtime(&delta_time);

	if (ctr_mode == MODE_TCTR) tfcrypt_getrandom(&tctx.tfc, sizeof(TFC_X(ctx)));
	else tfcrypt_getrandom(&tctx, sizeof(TF_X(ctx)));
	if (do_mac != NO) SK_X(init)(&sctx, macbits, NO);

	tf_nfsay(stdout, "%s: doing benchmark for %lu microseconds ... ", progname, useconds);

	while (1) {
		if (do_stop) break;

		total_processed_src += sizeof(srcblk);

		if (do_mac != NO) SK_X(update)(&sctx, srcblk, sizeof(srcblk));
		if (ctr_mode == MODE_CTR) TF_X(crypt)(&tctx, srcblk, sizeof(srcblk), srcblk);
		else if (ctr_mode == MODE_TCTR && do_edcrypt == DO_ENCRYPT)
			TF_X(tctr_encrypt)(&tctx.tfc, srcblk, sizeof(srcblk), srcblk);
		else if (ctr_mode == MODE_TCTR && do_edcrypt == DO_DECRYPT)
			TF_X(tctr_decrypt)(&tctx.tfc, srcblk, sizeof(srcblk), srcblk);
		else if (ctr_mode == MODE_CBC && do_edcrypt == DO_ENCRYPT)
			TF_X(cbc_encrypt)(&tctx, srcblk, sizeof(srcblk), srcblk);
		else if (ctr_mode == MODE_CBC && do_edcrypt == DO_DECRYPT)
			TF_X(cbc_decrypt)(&tctx, srcblk, sizeof(srcblk), srcblk);

		delta_processed += sizeof(srcblk);
	}
}

static void gen_write_bytes(const char *foutname, unsigned long long nrbytes, int do_random)
{
	int fd;
	size_t szt;
	unsigned char stack_data[sizeof(dstblk)];

	for (x = 1; x < NSIG; x++) signal(x, SIG_IGN);
	signal(SIGTERM, SIG_DFL);
	signal(SIGINT, SIG_DFL);
	memset(&sa, 0, sizeof(sa));
	sa.sa_flags = SA_RESTART;
	sa.sa_handler = print_crypt_status;
	sigaction(SIGUSR1, &sa, NULL);
	sigaction(SIGTSTP, &sa, NULL);
	if (quiet == NO) {
		sigaction(SIGINT, &sa, NULL);
		sigaction(SIGTERM, &sa, NULL);
	}
	sigaction(SIGALRM, &sa, NULL);
	if (status_timer) setup_next_alarm(status_timer);
	sa.sa_handler = change_status_width;
	sigaction(SIGQUIT, &sa, NULL);
	sa.sa_handler = change_status_timer;
	sigaction(SIGUSR2, &sa, NULL);
	memset(&sa, 0, sizeof(sa));

	getcurtime(&delta_time);

	if (do_less_stats) do_less_stats = NO;
	else do_less_stats = YES;

	if (!foutname) {
		fd = 1;
		foutname = STDOUT_NAME;
	}
	else if (!strcmp(foutname, "-")) {
		fd = 1;
		foutname = STDOUT_NAME;
	}
	else fd = open(foutname, O_WRONLY | O_CREAT | O_LARGEFILE | write_flags, 0666);
	if (fd == -1) xerror(NO, NO, YES, foutname);

	if (do_random == YES) {
		/*
		 * Clever coding warning: use of uninitialised stack data.
		 * You *may* remove it and there will be no *any* harm (really),
		 * it's just here because I can do it for additional randomness.
		 */
		memcpy(dstblk, stack_data, sizeof(stack_data));
		tfcrypt_getrandom(&tctx, sizeof(TF_X(ctx)));
	}
	else memset(dstblk, 0, sizeof(dstblk));
	if (do_random == NO) do_edcrypt = DO_PLAIN;

	if (verbose) tf_nfsay(stderr, "writing %lld bytes to %s ... ", nrbytes, foutname);

	errno = 0;
	while (1) {
		if (do_stop) break;
		szt = 0;
		lblock = BLK_LEN_ADJ(nrbytes, total_processed_src, sizeof(srcblk));
		if (lblock < TF_BLOCK_SIZE && ctr_mode != MODE_CTR) {
			/*
			 * If last block is not round - prevent automatic switching to CTR.
			 * Encrypt full block in specified mode, then just cut off garbage.
			 * This does not matter really, TF is excellent cipher by itself,
			 * but it's here for consistency and as additional protective measure.
			 */
			szt = lblock;
			lblock = TF_BLOCK_SIZE;
		}

		if (do_random == YES) {
			if (ctr_mode == MODE_CTR) TF_X(crypt)(&tctx, srcblk, lblock, dstblk);
			else if (ctr_mode == MODE_TCTR)
				TF_X(tctr_encrypt)(&tctx.tfc, srcblk, lblock, dstblk);
			else if (ctr_mode == MODE_CBC)
				TF_X(cbc_encrypt)(&tctx, srcblk, lblock, dstblk);
		}

		write(fd, dstblk, szt ? szt : lblock);
		if (errno) {
			switch (error_action) {
				case ERRACT_CONT: xerror(YES, NO, YES, foutname); break;
				/* ERRACT_SYNC not really useful! */
				default: xerror(NO, NO, YES, foutname); break;
			}
		}
		if (do_fsync) {
			errno = 0;
			fsync(fd);
			if (errno) {
				switch (error_action) {
					case ERRACT_CONT: xerror(YES, NO, YES, foutname); break;
					/* ERRACT_SYNC not really useful! */
					default: xerror(NO, NO, YES, foutname); break;
				}
			}
		}
		if (szt) lblock = szt;
		total_processed_src += lblock;
		delta_processed += lblock;
		total_processed_dst = total_processed_src;
		if (total_processed_src >= nrbytes) break;
	}

	if (verbose) tf_esay("done!");
	if (verbose || status_timer) print_crypt_status(0);

	xclose(fd);
	xexit(0);
}

int main(int argc, char **argv)
{
	double td;
	char *s, *d, *t;

	progname = basename(argv[0]);

	/* init some defaults */
	macbits = bits;
	if (!isatty(2)) do_statline_dynamic = NO;

	/* User did not given -E opt -- -sum256, so just do sums as usual. */
	if (argc > 1 && !strncmp(*(argv+1), "-sum", 4)) goto _do_hash;

	opterr = 0;
	while ((c = getopt(argc, argv, "aU:C:r:t:TK:Pkc:l:qedn:b:B:vV:pwE:O:S:AmM:R:Z:D:W")) != -1) {
		switch (c) {
			case 'r':
				randsource = optarg;
				break;
			case 'c':
				if (!strcasecmp(optarg, "show"))
					counter_opt = COUNTER_SHOW;
				else if (!strcasecmp(optarg, "head"))
					counter_opt = COUNTER_HEAD;
				else if (!strcasecmp(optarg, "rand"))
					counter_opt = COUNTER_RAND;
				else counter_file = optarg;
				break;
			case 'C':
				if (!strcasecmp(optarg, "ctr"))
					ctr_mode = MODE_CTR;
				else if (!strcasecmp(optarg, "tctr"))
					ctr_mode = MODE_TCTR;
				else if (!strcasecmp(optarg, "cbc"))
					ctr_mode = MODE_CBC;
				else xerror(NO, YES, YES, "%s: invalid mode of operation", optarg);
				break;
			case 'P':
				do_edcrypt = DO_PLAIN;
				password = YES; /* do not require dummy keyfile. */
				ctr_mode = MODE_PLAIN;
				break;
			case 'e':
				do_edcrypt = DO_ENCRYPT;
				break;
			case 'd':
				do_edcrypt = DO_DECRYPT;
				break;
			case 'D':
				macbits = strtol(optarg, &stoi, 10);
				if (macbits == 0 || *stoi || macbits < 8
				|| macbits > TF_MAX_BITS || macbits % 8)
					xerror(NO, YES, YES, "%s: invalid MAC bits setting", optarg);
				break;
			case 'n':
				passes = strtol(optarg, &stoi, 10);
				if (*stoi) xerror(NO, YES, YES, "%s: invalid number of passes", optarg);
				break;
			case 'b':
				bits = strtol(optarg, &stoi, 10);
				if (bits == 0 || *stoi || bits < 8
				|| bits > TF_MAX_BITS || bits % 8)
					xerror(NO, YES, YES, "%s: invalid bits setting", optarg);
				macbits = bits;
				break;
			case 't':
				tweakf = optarg;
				break;
			case 'T':
				if (do_secret_tweak) do_secret_tweak = NO;
				else do_secret_tweak = YES;
				break;
			case 'U':
				if (!strcasecmp(optarg, "key"))
					mackey_opt = MACKEY_RAWKEY;
				else if (!strcasecmp(optarg, "pwd"))
					mackey_opt = MACKEY_PASSWD;
				else {
					mackey_opt = MACKEY_FILE;
					mackeyf = optarg;
				}
				break;
			case 'p':
				password = YES;
				break;
			case 'k':
				rawkey = YES;
				break;
			case 'K':
				genkeyf = optarg;
				break;
			case 'l':
				maxlen = xpstrtoull(optarg, &stoi);
				if (*stoi) {
					maxlen = fnamesize(optarg, YES);
					if (maxlen == ULL_1) xerror(NO, YES, YES,
					"%s: invalid count value", optarg);
				}
				if (counter_opt == COUNTER_HEAD)
					maxlen += TF_BLOCK_SIZE;
				break;
			case 'w':
				overwrite_source = YES;
				break;
			case 'B':
				td = strtod(optarg, &stoi);
				do_benchmark = DTOUSECS(td);
				if (do_benchmark <= DTOUSECS(0) || *stoi)
					xerror(NO, YES, YES, "%s: invalid benchmark time in seconds", optarg);
				break;
			case 'E':
				if (!strcmp(optarg, "exit"))
					error_action = ERRACT_EXIT;
				else if (!strncmp(optarg, "cont", 4)) /* cont[inue] */
					error_action = ERRACT_CONT;
				else if (!strcmp(optarg, "sync"))
					error_action = ERRACT_SYNC;
				else xerror(NO, YES, YES, "invalid error action %s specified", optarg);
				break;
			case 'O':
				s = d = optarg; t = NULL;
				while ((s = strtok_r(d, ",", &t))) {
					if (d) d = NULL;
					if (!strcmp(s, "sync"))
						write_flags |= O_SYNC;
					else if (!strcmp(s, "trunc"))
						write_flags |= O_TRUNC;
					else if (!strcmp(s, "fsync"))
						do_fsync = YES;
					else if (!strcmp(s, "pad"))
						do_pad = YES;
					else if (!strcmp(s, "xtime"))
						do_preserve_time = YES;
					else if (!strcmp(s, "gibsize"))
						do_stats_in_gibs = YES;
					else if (!strcmp(s, "pstat"))
						do_statline_dynamic = NO;
					else if (!strcmp(s, "statless"))
						do_less_stats = YES;
					else if (!strncmp(s, "iseek", 5) && *(s+5) == '=') {
						s += 6;
						iseek = xpstrtoull(s, &stoi);
						/* Mayakovsky mode on... */
						if (*stoi)
							xerror(NO, YES, YES,
								"%s: invalid iseek value", s);
						if (ctr_mode != MODE_PLAIN && iseek % TF_BLOCK_SIZE)
							xerror(NO, YES, YES,
								"%s: not round to TF block size "
								"of %u bytes",
								s, TFC_U(TF_BLOCK_SIZE));
						iseek_blocks = iseek / TF_BLOCK_SIZE;
					}
					else if (!strncmp(s, "ixseek", 6) && *(s+6) == '=') {
						s += 7;
						iseek = xpstrtoull(s, &stoi);
						if (*stoi) xerror(NO, YES, YES,
							"%s: invalid ixseek value", s);
					}
					else if (!strncmp(s, "ictr", 4) && *(s+4) == '=') {
						s += 5;
						iseek_blocks = xpstrtoull(s, &stoi);
						if (*stoi) xerror(NO, YES, YES,
							"%s: invalid ictr value", s);
					}
					else if (!strncmp(s, "ixctr", 5) && *(s+5) == '=') {
						s += 6;
						iseek_blocks = xpstrtoull(s, &stoi);
						if (*stoi) xerror(NO, YES, YES,
							"%s: invalid ixctr value", s);
						if (iseek_blocks % TF_BLOCK_SIZE)
							xerror(NO, YES, YES,
							"%s: not round to TF block size "
							"of %u bytes", s, TFC_U(TF_BLOCK_SIZE));
						iseek_blocks /= TF_BLOCK_SIZE;
					}
					else if (!strncmp(s, "oseek", 5) && *(s+5) == '=') {
						s += 6;
						oseek = xpstrtoull(s, &stoi);
						if (*stoi) xerror(NO, YES, YES,
							"%s: invalid oseek value", s);
					}
					else if (!strncmp(s, "count", 5) && *(s+5) == '=') {
						s += 6;
						maxlen = xpstrtoull(s, &stoi);
						if (*stoi) {
							maxlen = fnamesize(s, YES);
							if (maxlen == ULL_1) xerror(NO, YES, YES,
							"%s: invalid count value", s);
						}
						if (counter_opt == COUNTER_HEAD)
							maxlen += TF_BLOCK_SIZE;
					}
					else if (!strncmp(s, "xkey", 4) && *(s+4) == '=') {
						s += 5;
						maxkeylen = xpstrtoull(s, &stoi);
						if (*stoi) {
							maxkeylen = (size_t)fnamesize(s, YES);
							if (maxkeylen == SIZET_1)
								xerror(NO, YES, YES,
								"%s: invalid key length value", s);
						}
					}
					else xerror(NO, YES, YES, "invalid option %s", s);
				}
				break;
			case 'S':
				do_mac = MAC_SIGN;
				if (strcasecmp(optarg, "mac") != 0)
					do_mac_file = optarg;
				break;
			case 'M':
				do_mac = MAC_VRFY;
				if (!strcasecmp(optarg, "drop"))
					do_mac = MAC_DROP;
				else if (strcasecmp(optarg, "mac") != 0)
					do_mac_file = optarg;
				break;
			case 'm':
				if (do_mac != MAC_VRFY)
					xerror(NO, YES, YES, "signature source was not specified");
				do_mac = MAC_JUST_VRFY;
				break;
			case 'R':
			case 'Z':
				{
					unsigned long long t;
					if (!strcasecmp(optarg, "bits"))
						t = TF_FROM_BITS(bits);
					else if (!strcasecmp(optarg, "cbs"))
						t = TF_BLOCK_SIZE;
					else if (!strcasecmp(optarg, "iobs"))
						t = BLKSIZE;
					else {
						t = xpstrtoull(optarg, &stoi);
						if (*stoi) t = fnamesize(optarg, NO);
					}
					if (c == 'Z') genzero_nr_bytes = t;
					else genrandom_nr_bytes = t;
				}
				break;
			case 'a':
				do_preserve_time = YES;
				break;
			case 'A':
				do_base64 = YES;
				break;
			case 'W':
				do_raw = YES;
				break;
			case 'q':
				quiet = YES;
				verbose = NO;
				status_timer = 0;
				break;
			case 'v':
				verbose = YES;
				break;
			case 'V':
				td = strtod(optarg, &stoi);
				status_timer = DTOUSECS(td);
				if (status_timer <= DTOUSECS(0) || *stoi) status_timer = 0;
				break;
			default:
				usage();
				break;
		}
	}

	/* noexit functions 1 */
	if (do_benchmark) do_benchmark_now(do_benchmark);
	if (genrandom_nr_bytes) gen_write_bytes(*(argv+optind), genrandom_nr_bytes, YES);
	if (genzero_nr_bytes) gen_write_bytes(*(argv+optind), genzero_nr_bytes, NO);

	/* Precautions. */
	if (rawkey && password)
		xerror(NO, YES, YES, "Cannot use rawkey and hashing password!");
	if (do_edcrypt == DO_ENCRYPT && do_mac >= MAC_VRFY)
		xerror(NO, YES, YES, "Cannot encrypt and verify signature!");
	if (do_edcrypt == DO_DECRYPT && do_mac == MAC_SIGN)
		xerror(NO, YES, YES, "Cannot decrypt and calculate signature!");
	if (do_mac == MAC_SIGN && do_base64 == YES && !do_mac_file)
		xerror(NO, YES, YES, "Only binary signatures are embedded into encrypted file!");
	if (do_edcrypt == DO_DECRYPT && counter_opt == COUNTER_RAND)
		xerror(NO, YES, YES, "Cannot decrypt and embed a generated CTR into file!");
	if (do_edcrypt == DO_ENCRYPT && counter_opt == COUNTER_HEAD)
		xerror(NO, YES, YES, "Cannot encrypt and read CTR from source!");
	if (overwrite_source && counter_opt == COUNTER_RAND)
		xerror(NO, YES, YES, "Cannot embed a CTR into file when overwriting it!");
	if (do_raw && do_base64)
		xerror(NO, YES, YES, "Only one output format can be at same time!");
	if (ctr_mode == MODE_PLAIN
	&& (do_edcrypt || do_mac || rawkey
	|| mackey_opt || counter_opt || counter_file))
		xerror(NO, YES, YES, "Encryption facility is disabled when in plain IO mode.");

	errno = 0;

	if (mackey_opt == MACKEY_FILE && mackeyf) { /* read custom MAC key - sksum uses it too. */
		int mkfd = -1, do_stop = NO;

		if (!strcmp(mackeyf, "-")) mkfd = 0;
		else mkfd = open(mackeyf, O_RDONLY | O_LARGEFILE);
		if (mkfd == -1) xerror(NO, NO, YES, mackeyf);

		SK_X(init_key)(&sctx);

		while (1) {
			if (do_stop) break;
			pblk = (unsigned char *)tmp_data;
			ldone = 0;
			lrem = lblock = sizeof(tmp_data);
_mkragain:		lio = read(mkfd, pblk, lrem);
			if (lio == 0) do_stop = YES;
			if (lio != SIZET_1) ldone += lio;
			if (errno) {
				switch (error_action) {
					case ERRACT_CONT: xerror(YES, NO, NO, mackeyf); break;
					case ERRACT_SYNC:
						xerror(YES, NO, NO, mackeyf);
						lio = ldone = lrem = lblock;
						memset(tmp_data, 0, lio);
						break;
					default: xerror(NO, NO, NO, mackeyf); break;
				}
			}
			if (lio && lio < lrem) {
				pblk += lio;
				lrem -= lio;
				goto _mkragain;
			}

			SK_X(update_key)(&sctx, tmp_data, ldone);
		}

		SK_X(final_key)(&sctx);

		xclose(mkfd);
	}
	else if (mackey_opt == MACKEY_PASSWD) {
		size_t n;

		memset(&getps, 0, sizeof(struct getpasswd_state));
		getps.fd = getps.efd = -1;
		getps.passwd = pwdask;
		getps.pwlen = sizeof(pwdask)-1;
		getps.echo = "Enter MAC password: ";
		getps.charfilter = getps_filter;
		getps.maskchar = 'x';
		if (xgetpasswd(&getps) == (size_t)-1) xexit(1);
		n = strnlen(pwdask, sizeof(pwdask)-1);
		SK_X(init_key)(&sctx);
		SK_X(update_key)(&sctx, pwdask, n);
		SK_X(final_key)(&sctx);
		if (verbose) {
			unsigned char hint[2];
			skeinX(pwdask, n, hint, TF_TO_BITS(sizeof(hint)));
			tf_nfsay(stderr, "MAC password hint: ");
			binhex(stderr, hint, sizeof(hint), 1);
			memset(hint, 0, sizeof(hint));
		}
	}

_do_hash: /* noexit functions 2 */
	if ((strlen(progname) <= 9)
	&& ((!strcmp(progname, "sksum")) /* sksum */
	|| ((!memcmp(progname, "sk", 2)) /* ^sk ... */
	&& (!memcmp(progname+3, "sum", 3) /* sk8|sum */
	|| !memcmp(progname+4, "sum", 3) /* sk96|sum */
	|| !memcmp(progname+5, "sum", 3) /* sk512|sum */
	|| !memcmp(progname+6, "sum", 3))))) /* sk1024|sum */
		do_sksum(progname, argv+optind, do_base64, do_raw);
	for (x = 0; x < argc; x++)
		if (!strncmp(argv[x], "-sum", 4)) do_sksum(argv[x], argv+(x+1), do_base64, do_raw);
	if (!strncmp(progname, "base64", 6)) do_edbase64(progname, argv+optind);
	for (x = 0; x < argc; x++)
		if (!strncmp(argv[x], "-b64", 4)) do_edbase64(argv[x], argv+(x+1));

	idx = optind;

	if (!strcmp(progname, "tfsign") && argv[idx] && do_edcrypt == DO_ENCRYPT) {
		int t = NO;
		maxlen = TF_FROM_BITS(macbits);
		stoi = NULL;
		iseek_blocks = xpstrtoull(argv[idx], &stoi);
		if (*stoi) iseek_blocks = fnamesize(argv[idx], NO);
		if (iseek_blocks % TF_BLOCK_SIZE) t = YES;
		iseek_blocks /= TF_BLOCK_SIZE;
		if (t) iseek_blocks++;
		if (counter_file && iseek_blocks > 0) iseek_blocks--;
		if (verbose) tf_esay("setting CTR block number to %llu", iseek_blocks);

		idx++;
	}

/* keyfile */
	if (argv[idx] && !password) {
		if (!strcmp(argv[idx], "-")) kfd = 0;
		else kfd = open(argv[idx], O_RDONLY | O_LARGEFILE);
		if (kfd == -1) xerror(NO, NO, YES, argv[idx]);

		/* hide key filename from ps(1) */
		lio = strnlen(argv[idx], PATH_MAX);
		memset(argv[idx], '*', lio);

		idx++;
	}
	else password = YES;

	errno = 0;
	if (tweakf) { /* read custom tweak */
		int twfd;
		if (!strcmp(tweakf, "-")) twfd = 0;
		else twfd = open(tweakf, O_RDONLY | O_LARGEFILE);
		if (twfd == -1) xerror(NO, NO, YES, tweakf);
		lio = ldone = read(twfd, xtweak, sizeof(xtweak));
		if (errno) xerror(NO, NO, YES, tweakf);
		if (ldone < sizeof(xtweak))
			xerror(NO, NO, YES, "%s: %zu bytes tweak required", tweakf, sizeof(xtweak));
		xclose(twfd);
	}

	errno = 0;
/* source file/stream */
	if (argv[idx]) {
		if (!strcmp(argv[idx], "-") && kfd) sfd = 0;
		else {
			sfd = open(argv[idx], O_RDONLY | O_LARGEFILE);
			if (do_preserve_time) if (fstat(sfd, &s_stat) == -1)
				xerror(YES, NO, YES, "stat(%s)", argv[idx]);
		}
		if (sfd == -1) xerror(NO, NO, YES, argv[idx]);

		if (do_edcrypt == DO_DECRYPT && do_mac != NO && maxlen != ULL_1) {
			if (verbose) tf_esay("Disabling signature verification on "
						"requested partial decryption.");
			do_mac = NO;
		}

		if ((do_mac >= MAC_VRFY || do_mac == MAC_DROP) && !do_mac_file) {
			maxlen = (unsigned long long)fdsize(sfd);
			if (maxlen == ULL_1)
				xerror(NO, YES, YES,
				"Cannot verify embedded MAC with non-seekable source!");
			maxlen -= TF_FROM_BITS(macbits);
		}
		srcfname = argv[idx];
		idx++;
	}

	if (!do_mac_file && (do_mac >= MAC_VRFY && sfd == 0))
		xerror(NO, YES, YES, "Cannot verify embedded MAC with non-seekable source!");

	ctrsz = (ctr_mode != MODE_TCTR) ? TF_BLOCK_SIZE : sizeof(tctx.tfc.T);

	errno = 0;
	if (counter_file) { /* read an initial CTR from separate file */
		int ctrfd;
		if (!strcmp(counter_file, "-")) ctrfd = 0;
		else ctrfd = open(counter_file, O_RDONLY | O_LARGEFILE);
		if (ctrfd == -1) xerror(NO, NO, YES, counter_file);
		lio = read(ctrfd, counter, sizeof(counter));
		if (errno) xerror(NO, NO, YES, counter_file);
		if (lio < TF_KEY_SIZE) xerror(NO, YES, YES, "counter file is too small (%zu)!", lio);
		xclose(ctrfd);
	}
	else if (counter_opt == COUNTER_HEAD) { /* read an initial CTR from beginning of source stream */
		pblk = counter;
		ldone = 0;
		lrem = lblock = ctrsz;
_ctrragain:	lio = read(sfd, pblk, lrem);
		if (lio != SIZET_1) ldone += lio;
		if (errno) {
			switch (error_action) {
				case ERRACT_CONT: xerror(YES, NO, NO, srcfname); break;
				case ERRACT_SYNC:
					xerror(YES, NO, NO, srcfname);
					lio = ldone = lrem = lblock;
					memset(counter, 0, lio);
					break;
				default: xerror(NO, NO, NO, srcfname); break;
			}
		}
		if (lio && lio < lrem) {
			pblk += lio;
			lrem -= lio;
			goto _ctrragain;
		}
		total_processed_src += ldone;
	}

	if (iseek) {
		if (counter_opt == COUNTER_HEAD)
			iseek += ctrsz;
		if (lseek(sfd, iseek, SEEK_SET) == -1)
			xerror(YES, NO, NO, "%s: seek failed", srcfname);
	}

	if (ctr_mode == MODE_PLAIN) goto _plain;

	if (verbose) tf_esay("hashing password");

	if (rawkey) { /* read raw key instead of playing with derivation */
		pblk = key;
		ldone = 0;
		lrem = lblock = TF_FROM_BITS(bits);
_keyragain:	lio = read(kfd, pblk, lrem);
		if (lio != SIZET_1) ldone += lio;
		if (errno) {
			switch (error_action) {
				case ERRACT_CONT: xerror(YES, NO, NO, "reading key"); break;
				case ERRACT_SYNC:
					xerror(YES, NO, NO, "reading key");
					lio = ldone = lrem = lblock;
					memset(key, 0, lio);
					break;
				default: xerror(NO, NO, NO, "reading key"); break;
			}
		}
		if (lio && lio < lrem) {
			pblk += lio;
			lrem -= lio;
			goto _keyragain;
		}
		if (ldone < lblock) xerror(NO, YES, YES, "rawkey too small! (%zu)", ldone);
	}
	else if (password) { /* password read and derivation */
_pwdagain:	memset(&getps, 0, sizeof(struct getpasswd_state));
		getps.fd = getps.efd = -1;
		getps.passwd = pwdask;
		getps.pwlen = sizeof(pwdask)-1;
		getps.echo = "Enter password: ";
		getps.charfilter = getps_filter;
		getps.maskchar = 'x';
		if (xgetpasswd(&getps) == (size_t)-1) xexit(1);
		if (do_edcrypt == DO_ENCRYPT) {
			getps.fd = getps.efd = -1;
			getps.passwd = pwdagain;
			getps.pwlen = sizeof(pwdagain)-1;
			getps.echo = "Enter it again: ";
			if (xgetpasswd(&getps) == (size_t)-1) xexit(1);
			if (strncmp(pwdask, pwdagain, sizeof(pwdagain)-1) != 0) {
				tf_esay("Passwords are different, try again");
				goto _pwdagain;
			}
		}
		skeinX((const unsigned char*)pwdask, strnlen(pwdask, sizeof(pwdask)-1), key, bits);
		memset(pwdask, 0, sizeof(pwdask));
		memset(pwdagain, 0, sizeof(pwdagain));
	}
	else { /* hash a keyfile */
		if (skeinfd(kfd, maxkeylen, mackey_opt ? &sctx : NULL, key, bits) != YES)
			xerror(NO, NO, YES, "hashing key");
	}

	if (passes > 1 && !rawkey) /* derivation actually goes here */
		skein_loop(key, TF_FROM_BITS(bits), key, bits, passes);

	if (genkeyf) { /* save a generated rawkey to file and exit */
		int krfd;
		if (!strcmp(genkeyf, "-")) krfd = 1;
		else krfd = open(genkeyf, O_WRONLY | O_CREAT | O_LARGEFILE | write_flags, 0666);
		if (krfd == -1) xerror(NO, NO, YES, genkeyf);
		write(krfd, key, TF_FROM_BITS(bits));
		if (errno) {
			switch (error_action) {
				case ERRACT_CONT: xerror(YES, NO, YES, genkeyf); break;
				/* ERRACT_SYNC not really useful! */
				default: xerror(NO, NO, YES, genkeyf); break;
			}
		}
		if (do_fsync) {
			errno = 0;
			fsync(krfd);
			if (errno) {
				switch (error_action) {
					case ERRACT_CONT: xerror(YES, NO, YES, genkeyf); break;
					/* ERRACT_SYNC not really useful! */
					default: xerror(NO, NO, YES, genkeyf); break;
				}
			}
		}
		xclose(krfd);
		if (verbose) {
			tf_esay("password hashing done");
			tf_esay("rawkey written to %s.", genkeyf);
			tf_esay("Have a nice day!");
		}
		xexit(0);
	}

	if (ctr_mode == MODE_TCTR) TFC_X(init)(&tctx.tfc);
	else TF_X(init)(&tctx);
	TFC_X(set_key)(&tctx.tfc, key, TF_FROM_BITS(bits));
	if (!counter_file && counter_opt <= COUNTER_SHOW)
		skeinX(key, sizeof(key), counter, TF_TO_BITS(ctrsz));
	switch (counter_opt) {
		case COUNTER_SHOW:
			if (do_base64) binb64(stderr, counter, ctrsz, 1);
			else if (do_raw) write(2/*stderr*/, counter, ctrsz);
			else binhex(stderr, counter, ctrsz, 1);
			break;
		case COUNTER_RAND: tfcrypt_getrandom(counter, ctrsz); break; /* will be written later */
		default: break; /* 2 apply here, no action */
	}
	if (do_secret_tweak) {
		skeinX(key, sizeof(key), xtweak, TF_TO_BITS(sizeof(xtweak)));
		TFC_X(set_tweak)(&tctx.tfc, xtweak);
	}
	else TFC_X(set_tweak)(&tctx.tfc, tweakf ? xtweak : tweak);
	if (ctr_mode == MODE_TCTR) {
		TF_X(start_counter_tctr)(&tctx.tfc, counter);
		if (iseek_blocks) {
			if (do_edcrypt == DO_DECRYPT && do_mac != NO) {
				if (verbose) tf_esay("Disabling signature verification on "
							"requested partial decryption.");
				do_mac = NO;
			}
			TF_X(rewind_counter_tctr)(&tctx.tfc, &iseek_blocks, 1);
		}
	}
	else {
		TF_X(start_counter)(&tctx, counter);
		if (iseek_blocks) {
			if (do_edcrypt == DO_DECRYPT && do_mac != NO) {
				if (verbose) tf_esay("Disabling signature verification on "
							"requested partial decryption.");
				do_mac = NO;
			}
			TF_X(rewind_counter)(&tctx, &iseek_blocks, 1);
		}
	}

	if (do_mac != NO) {
		if (verbose) tf_esay("doing MAC calculation, processing speed will be slower.");
		if (mackey_opt == MACKEY_RAWKEY) {
			SK_X(init_key)(&sctx);
			SK_X(update_key)(&sctx, key, TF_KEY_SIZE);
			SK_X(final_key)(&sctx);
			SK_X(init)(&sctx, macbits, YES);
		}
		/* passwd && file already preinited */
		else SK_X(init)(&sctx, macbits, YES);
	}

	memset(key, 0, sizeof(key));

	if (!password) {
		xclose(kfd);
		kfd = -1;
	}
	if (verbose) tf_esay("password hashing done");

	if (overwrite_source && srcfname) argv[idx] = srcfname;

_plain:
/* destination is just sink where we dump all encrypted data */
	if (argv[idx]) {
		if (!strcmp(argv[idx], "-")) dfd = 1;
		else dfd = open(argv[idx], O_RDWR | O_LARGEFILE | write_flags, 0666);
		if (dfd == -1) {
			dfd = open(argv[idx], O_WRONLY | O_CREAT | O_LARGEFILE | write_flags, 0666);
			if (dfd == -1) xerror(NO, NO, YES, argv[idx]);
		}
		dstfname = argv[idx];
		idx++;
	}

	if (oseek) {
		if (lseek(dfd, oseek, SEEK_SET) == -1)
			xerror(YES, NO, NO, "%s: seek failed", dstfname);
	}

	for (x = 1; x < NSIG; x++) signal(x, SIG_IGN);
	signal(SIGTERM, SIG_DFL);
	signal(SIGINT, SIG_DFL);
	memset(&sa, 0, sizeof(sa));
	sa.sa_flags = SA_RESTART;
	sa.sa_handler = print_crypt_status;
	sigaction(SIGUSR1, &sa, NULL);
	sigaction(SIGTSTP, &sa, NULL);
	if (quiet == NO) {
		sigaction(SIGINT, &sa, NULL);
		sigaction(SIGTERM, &sa, NULL);
	}
	sigaction(SIGALRM, &sa, NULL);
	if (status_timer) setup_next_alarm(status_timer);
	sa.sa_handler = change_status_width;
	sigaction(SIGQUIT, &sa, NULL);
	sa.sa_handler = change_status_timer;
	sigaction(SIGUSR2, &sa, NULL);
	memset(&sa, 0, sizeof(sa));

	getcurtime(&delta_time);

	errno = 0;
	if (counter_opt == COUNTER_RAND) { /* write a random CTR to beginning of stream */
		pblk = counter;
		lio = lrem = ctrsz;
		ldone = 0;
_ctrwagain:	lio = write(dfd, pblk, lrem);
		if (lio != SIZET_1) ldone += lio;
		if (errno) {
			switch (error_action) {
				case ERRACT_CONT: xerror(YES, NO, NO, dstfname); break;
				default: xerror(NO, NO, NO, dstfname); break;
			}
		}
		if (do_fsync) {
			errno = 0;
			fsync(dfd);
			if (errno) {
				switch (error_action) {
					case ERRACT_CONT: xerror(YES, NO, NO, dstfname); break;
					default: xerror(NO, NO, NO, dstfname); break;
				}
			}
		}
		if (lio < lrem) {
			pblk += lio;
			lrem -= lio;
			goto _ctrwagain;
		}
		total_processed_dst += ldone;
		delta_processed += ldone;
	}
	memset(counter, 0, sizeof(counter));

	errno = 0;
	while (1) {
		if (do_stop) break;
		pblk = srcblk;
		ldone = 0;
		lrem = lblock = BLK_LEN_ADJ(maxlen, total_processed_src, sizeof(srcblk));
_ragain:	lio = read(sfd, pblk, lrem);
		if (lio == 0) do_stop = STOP_BEGAN;
		if (lio != SIZET_1) ldone += lio;
		if (errno) {
			switch (error_action) {
				case ERRACT_CONT: xerror(YES, NO, NO, srcfname); break;
				case ERRACT_SYNC:
					xerror(YES, NO, NO, srcfname);
					lio = ldone = lrem = lblock;
					memset(srcblk, 0, lio);
					break;
				default: xerror(NO, NO, NO, srcfname); break;
			}
		}
		if (lio && lio < lrem) {
			pblk += lio;
			lrem -= lio;
			goto _ragain;
		}
		total_processed_src += ldone;

		if (do_pad && (ldone % TF_BLOCK_SIZE)) {
			size_t orig = ldone;
			ldone += (TF_BLOCK_SIZE - (ldone % TF_BLOCK_SIZE));
			if (ldone > sizeof(srcblk)) ldone = sizeof(srcblk);
			memset(srcblk+orig, 0, sizeof(srcblk)-orig);
		}

		if (do_mac == MAC_SIGN) SK_X(update)(&sctx, srcblk, ldone);
		if (ctr_mode == MODE_CTR) TF_X(crypt)(&tctx, srcblk, ldone, dstblk);
		else if (ctr_mode == MODE_TCTR && do_edcrypt == DO_ENCRYPT)
			TF_X(tctr_encrypt)(&tctx.tfc, srcblk, ldone, dstblk);
		else if (ctr_mode == MODE_TCTR && do_edcrypt == DO_DECRYPT)
			TF_X(tctr_decrypt)(&tctx.tfc, srcblk, ldone, dstblk);
		else if (ctr_mode == MODE_CBC && do_edcrypt == DO_ENCRYPT)
			TF_X(cbc_encrypt)(&tctx, srcblk, ldone, dstblk);
		else if (ctr_mode == MODE_CBC && do_edcrypt == DO_DECRYPT)
			TF_X(cbc_decrypt)(&tctx, srcblk, ldone, dstblk);
		else if (ctr_mode == MODE_PLAIN)
			memcpy(dstblk, srcblk, ldone);
		if (do_mac >= MAC_VRFY) {
			SK_X(update)(&sctx, dstblk, ldone);
			if (do_mac == MAC_JUST_VRFY) goto _nowrite;
		}

		pblk = dstblk;
		/* len and tt are same until partial write */
		lrem = ldone;
		ldone = 0;
_wagain:	lio = write(dfd, pblk, lrem);
		if (lio != SIZET_1) ldone += lio;
		if (errno) {
			switch (error_action) {
				case ERRACT_CONT: xerror(YES, NO, NO, dstfname); break;
				/* ERRACT_SYNC not really useful! */
				default: xerror(NO, NO, NO, dstfname); break;
			}
		}
		if (do_fsync) {
			errno = 0;
			fsync(dfd);
			if (errno) {
				switch (error_action) {
					case ERRACT_CONT: xerror(YES, NO, NO, dstfname); break;
					/* ERRACT_SYNC not really useful! */
					default: xerror(NO, NO, NO, dstfname); break;
				}
			}
		}
		if (lio < lrem) {
			pblk += lio;
			lrem -= lio;
			goto _wagain;
		}
_nowrite:	total_processed_dst += ldone;
		delta_processed += ldone;

		if (maxlen != ULL_1 && total_processed_src >= maxlen) break;
	}

	/* We're interrupted by signal: do not write anything. */
	if (do_stop == STOP_FULL) goto _nomac;

	errno = 0;
	/* read, decrypt and verify attached mac, if any */
	if (do_mac >= MAC_VRFY) {
		if (!do_mac_file) { /* read from end of file */
			pblk = counter; /* reuse "counter" and "key" space */
			ldone = 0;
			lrem = lblock = TF_FROM_BITS(macbits);
_macragain:		lio = read(sfd, pblk, lrem);
			if (lio != SIZET_1) ldone += lio;
			if (errno) {
				switch (error_action) {
					case ERRACT_CONT: xerror(YES, NO, NO, srcfname); break;
					case ERRACT_SYNC:
						xerror(YES, NO, NO, srcfname);
						lio = ldone = lrem = lblock;
						memset(counter, 0, lio);
						break;
					default: xerror(NO, NO, NO, srcfname); break;
				}
			}
			if (lio && lio < lrem) {
				pblk += lio;
				lrem -= lio;
				goto _macragain;
			}
			total_processed_src += ldone;
		}
		else { /* read from separate file */
			int mfd;
			if (!strcmp(do_mac_file, "-")) mfd = 0;
			else mfd = open(do_mac_file, O_RDONLY | O_LARGEFILE);
			if (mfd == -1) xerror(YES, NO, NO, do_mac_file); /* do not fail there */
			lio = ldone = read(mfd, tmp_data, sizeof(tmp_data));
			if (errno) xerror(NO, NO, YES, do_mac_file);
			if (!memcmp(tmp_data, ASCII_MAC_FOURCC, ASCII_MAC_FOURCC_LEN)) {
				memmove(tmp_data, tmp_data+ASCII_MAC_FOURCC_LEN,
					sizeof(tmp_data)-ASCII_MAC_FOURCC_LEN);
				lio = TF_FROM_BITS(macbits);
				base64_decode((char *)counter, lio,
					tmp_data, sizeof(tmp_data));
			}
			else memcpy(counter, tmp_data, TF_FROM_BITS(macbits));
			xclose(mfd);
		}

		if (ldone < TF_FROM_BITS(macbits)) {
			if (quiet == NO) tf_esay("short signature (%zu), not verifying", ldone);
			exitcode = 1;
			goto _shortmac;
		}

		SK_X(final)(&sctx, key); /* reuse "counter" and "key" space */
		if (ctr_mode == MODE_CTR) TF_X(crypt)(&tctx, counter, TF_FROM_BITS(macbits), tmp_data);
		else if (ctr_mode == MODE_TCTR)
			TF_X(tctr_decrypt)(&tctx.tfc, counter, TF_FROM_BITS(macbits), tmp_data);
		else if (ctr_mode == MODE_CBC)
			TF_X(cbc_decrypt)(&tctx, counter, TF_FROM_BITS(macbits), tmp_data);

		if (!memcmp(key, tmp_data, TF_FROM_BITS(macbits))) {
			if (quiet == NO) {
				tf_esay("signature is good");
				if (verbose) {
					if (do_base64) binb64(stderr, key, TF_FROM_BITS(macbits), 1);
					/* not emitting raw signature here, just hex */
					else binhex(stderr, key, TF_FROM_BITS(macbits), 1);
				}
			}
		}
		else {
			if (quiet == NO) tf_esay("signature is BAD: "
				"wrong password, key, or file is not signed");
			exitcode = 1;
		}

_shortmac:
		memset(key, 0, sizeof(key));
		memset(counter, 0, sizeof(counter));
		memset(tmp_data, 0, sizeof(tmp_data));
	}

	/* write an integrity total hash sum, in encrypted form */
	else if (do_mac == MAC_SIGN) {
		SK_X(final)(&sctx, key); /* reuse "counter" and "key" space */
		if (ctr_mode == MODE_CTR) TF_X(crypt)(&tctx, key, TF_FROM_BITS(macbits), counter);
		else if (ctr_mode == MODE_TCTR)
			TF_X(tctr_encrypt)(&tctx.tfc, key, TF_FROM_BITS(macbits), counter);
		else if (ctr_mode == MODE_CBC)
			TF_X(cbc_encrypt)(&tctx, key, TF_FROM_BITS(macbits), counter);
		memset(key, 0, sizeof(key));

		if (!do_mac_file) { /* not writing to separate file */
			pblk = counter; lio = lrem = TF_FROM_BITS(macbits);
			ldone = 0;
_macwagain:		lio = write(dfd, pblk, lrem);
			if (lio != SIZET_1) ldone += lio;
			if (errno) {
				switch (error_action) {
					case ERRACT_CONT: xerror(YES, NO, NO, dstfname); break;
					default: xerror(NO, NO, NO, dstfname); break;
				}
			}
			if (do_fsync) {
				errno = 0;
				fsync(dfd);
				if (errno) {
					switch (error_action) {
						case ERRACT_CONT: xerror(YES, NO, NO, dstfname); break;
						default: xerror(NO, NO, NO, dstfname); break;
					}
				}
			}
			if (lio < lrem) {
				pblk += lio;
				lrem -= lio;
				goto _macwagain;
			}
			total_processed_dst += ldone;
			delta_processed += ldone;
		}
		else { /* write to separate file */
			int mfd;
			if (!strcmp(do_mac_file, "-")) mfd = 1;
			else mfd = open(do_mac_file, O_WRONLY | O_CREAT | O_LARGEFILE | write_flags, 0666);
			if (mfd == -1) xerror(YES, NO, NO, do_mac_file); /* do not fail there */
			if (do_base64) {
				memcpy(tmp_data, ASCII_MAC_FOURCC, ASCII_MAC_FOURCC_LEN);
				base64_encode(tmp_data+ASCII_MAC_FOURCC_LEN, (char *)counter, TF_FROM_BITS(macbits));
				lio = strnlen(tmp_data, sizeof(tmp_data));
				write(mfd, tmp_data, lio);
				write(mfd, "\n", 1); /* Add a newline. */
			}
			else write(mfd, counter, TF_FROM_BITS(macbits));
			if (errno) {
				switch (error_action) {
					case ERRACT_CONT: xerror(YES, NO, YES, do_mac_file); break;
					/* ERRACT_SYNC not really useful! */
					default: xerror(NO, NO, YES, do_mac_file); break;
				}
			}
			if (do_fsync) {
				errno = 0;
				fsync(mfd);
				if (errno) {
					switch (error_action) {
						case ERRACT_CONT: xerror(YES, NO, YES, do_mac_file); break;
						/* ERRACT_SYNC not really useful! */
						default: xerror(NO, NO, YES, do_mac_file); break;
					}
				}
			}
			xclose(mfd);
		}

		memset(counter, 0, sizeof(counter));
	}

_nomac:
	if (verbose || status_timer) print_crypt_status(0);

	if (do_preserve_time) fcopy_matime(dfd, &s_stat);
	xclose(sfd);
	xclose(dfd);

	xexit(exitcode);
	return -1;
}
