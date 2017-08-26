VERSION:=$(shell cat VERSION)
override CFLAGS+=-D_TFCRYPT_VERSION=\"$(VERSION)\" -Wall -O2
UPX=upx

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)

all: tfcrypt

%: %.c VERSION
	$(CC) $(CFLAGS) -o $@ $<

tfcrypt: $(OBJS)
	$(CC) $(CFLAGS) $(LDFLAGS) $(OBJS) -o $@

tfcrypt.upx: $(OBJS)
	$(CC) $(CFLAGS) $(LDFLAGS) -static -s $(OBJS) -o $@
	$(UPX) --best $@

clean:
	rm -f *.o tfcrypt tfcrypt.upx
