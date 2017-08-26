#ifndef _TFCRYPT_H
#define _TFCRYPT_H

#include "base64.h"

#include "tf1024.h"
#undef __TF_X
#undef _TF_X
#undef TF_X
#undef TFC_X
#undef SK_X
#define __TF_X(x, y, z)	x ## y ## z
#define _TF_X(x, y, z) __TF_X(x, y, z)
#define TF_BITS_PFX	1024 /* redefine this to other TF bits version. */
#define TF_X(x)		_TF_X(tf,  TF_BITS_PFX, _ ## x)
#define TFC_X(x)	_TF_X(tfc, TF_BITS_PFX, _ ## x)
#define SK_X(x)		_TF_X(sk,  TF_BITS_PFX, _ ## x)
#define skeinX		_TF_X(sk,  TF_BITS_PFX, /* empty */)

#ifndef BLKSIZE
#define BLKSIZE 65536
#endif

#ifndef B64_WIDTH
#define B64_WIDTH 76
#endif
#define B64_EWIDTH (B64_WIDTH - (B64_WIDTH / 4))
#define B64_DWIDTH BLKSIZE

#define SIZET_1 ((size_t)-1)
#define ULL_1 ((unsigned long long)-1)

#define ASCII_MAC_FOURCC "%MAC"
#define ASCII_MAC_FOURCC_LEN (sizeof(ASCII_MAC_FOURCC)-1)

#define TFC_U(x) ((unsigned)x)
#define DTOUSECS(x) ((x) * 1000000.0)

#define DEFAULT_RANDSOURCE "/dev/urandom"
#define STDIN_NAME "(stdin)"
#define STDOUT_NAME "(stdout)"

static const char *size_scale[] = {"B", "K", "M", "G", "T", "P"};

size_t xstrlcpy(char *dst, const char *src, size_t size);

static void xerror(int noexit, int noerrno, int nostats, const char *fmt, ...);
static void print_crypt_status(int signal);

#undef YES
#undef NO
#define YES		1
#define NO		0

#define ERRACT_EXIT	0
#define ERRACT_CONT	1
#define ERRACT_SYNC	2

#define STOP_BEGAN	1
#define STOP_FULL	2

#define DO_PLAIN	0
#define DO_ENCRYPT	1
#define DO_DECRYPT	2

#define MAC_DROP	-1
#define MAC_SIGN	1
#define MAC_VRFY	2
#define MAC_JUST_VRFY	3

#define MACKEY_RAWKEY	1
#define MACKEY_PASSWD	2
#define MACKEY_FILE	3

#define MODE_PLAIN	-1
#define MODE_CTR	1
#define MODE_TCTR	3
#define MODE_CBC	4

#define COUNTER_SHOW	1
#define COUNTER_HEAD	2
#define COUNTER_RAND	3

#endif
