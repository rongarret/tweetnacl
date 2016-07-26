#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "tweetnacl.h"
#include "tweetnacl-aux.h"

void randombytes(u8 *s, u64 n) {
  FILE *f = fopen("/dev/urandom", "r");
  fread(s, n, 1, f);
  fclose(f);
}

FILE* f;

extern int crypto_hash_stream_read_block(u8* buf) {
  return fread(buf, 1, 128, f);
}

int main(int argc, char *argv[]) {

  if (argc<2) {
    printf("Usage: %s [file]\n", argv[0]);
    exit(-1);
  }

  f = fopen(argv[1], "r");
  fseeko(f, 0, SEEK_END);
  size_t n = ftello(f);
  rewind(f);
  string m = malloc(n);
  u64 mlen = fread((void*)m, 1, n, f);
  if (n!=mlen) {
    fprintf(stderr, "Input length mismatch: %lld %ld\n", mlen, n);
    exit(-1);
  }
  printf("Hashing %lld bytes\n\n", mlen);

  u8 h[crypto_hash_BYTES];
  crypto_hash(h, m, mlen);

  printf("crypto_hash:\n");
  for (int i=0; i<crypto_hash_BYTES; i++) printf("%02x", h[i]);
  printf("\n\n");

  rewind(f);
  hash_state hs;
  crypto_hash_stream(h, &hs);
  fclose(f);
  printf("crypto_hash_stream:\n");
  for (int i=0; i<crypto_hash_BYTES; i++) printf("%02x", h[i]);
  printf("\n\n");

  printf("shasum -a 512:\n");
  char buf[1024];
  sprintf(buf, "shasum -a 512 %s", argv[1]);
  system(buf);
}
