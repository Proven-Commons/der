/*
  The OpenSSL oracle for tests/run_tests.py: the BER reader of libcrypto
  (ASN1_get_object, d2i_ASN1_TYPE, d2i_ASN1_INTEGER, d2i_ASN1_NULL),
  driven line by line. It is built against the system library, whose
  version tests/run_tests.py checks.

  Each line of standard input is one request in the form `der serve`
  reads (octets in lower-case hex, `-` for none; integers in decimal),
  and each answer is in the form it writes: "OK ..." or "FAIL". A request
  the library cannot answer is answered "n/a", and a line this program
  cannot read "error". A line may end in LF or CR LF.

    decode HEX     the element at the start of the octets, and the rest
    all HEX        the element that is the whole input
    readint HEX    the integer that contents octets encode
    writeint INT   the contents octets of an integer
    encode TREE    n/a
    valid TREE     n/a
    version        "OK" and the version of the library that runs

  ASN1_get_object reads the identifier and length octets of each element,
  given the octets left in the input or in the element around it. It
  reads BER: the indefinite length for a constructed element, lengths not
  in the fewest octets, and tag numbers below 31 in the high form. A
  constructed element's contents are read the same way, element by
  element: to the end of its length, or, for the indefinite length, to
  the end-of-contents octets 00 00 (X.690 8.1.5), which are not part of
  the tree. An element of the universal class with number 1, 2 or 5 must
  also be read by d2i_ASN1_TYPE as a BOOLEAN, by d2i_ASN1_INTEGER, or by
  d2i_ASN1_NULL, given the same octets. The walk keeps its own stack, so
  deep nesting does not use the machine stack.

  readint frames the contents octets as an INTEGER element (the length
  octets are written here), reads it with d2i_ASN1_INTEGER and prints it
  with ASN1_INTEGER_to_BN and BN_bn2dec. writeint reads the integer with
  BN_dec2bn, writes it with BN_to_ASN1_INTEGER and i2d_ASN1_INTEGER, and
  prints the contents octets of what that writes.
*/

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <openssl/asn1.h>
#include <openssl/bn.h>
#include <openssl/crypto.h>
#include <openssl/err.h>

/* A growing text buffer. */
typedef struct {
  char *s;
  size_t n, cap;
} buf_t;

static void put(buf_t *b, const char *s, size_t n) {
  if (b->n + n + 1 > b->cap) {
    b->cap = 2 * (b->n + n + 1);
    b->s = realloc(b->s, b->cap);
    if (b->s == NULL) abort();
  }
  memcpy(b->s + b->n, s, n);
  b->n += n;
  b->s[b->n] = 0;
}

static void puts_(buf_t *b, const char *s) { put(b, s, strlen(s)); }

static void put_hex(buf_t *b, const unsigned char *p, long n) {
  static const char digits[] = "0123456789abcdef";
  if (n == 0) {
    puts_(b, "-");
    return;
  }
  for (long k = 0; k < n; ++k) {
    char two[2] = {digits[p[k] >> 4], digits[p[k] & 15]};
    put(b, two, 2);
  }
}

static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}

/* The octets of a field, in a new buffer, with their number in *len;
   NULL for a field that is not `-` or lower-case hex digits in pairs. */
static unsigned char *field(const char *f, long *len) {
  size_t n = strlen(f);
  unsigned char *out;
  if (strcmp(f, "-") == 0) {
    *len = 0;
    return calloc(1, 1);
  }
  if (n == 0 || n % 2 != 0) return NULL;
  out = calloc(n / 2 + 1, 1);
  for (size_t j = 0; j < n / 2; ++j) {
    int hi = hexval(f[2 * j]), lo = hexval(f[2 * j + 1]);
    if (hi < 0 || lo < 0) {
      free(out);
      return NULL;
    }
    out[j] = (unsigned char) (hi * 16 + lo);
  }
  *len = (long) (n / 2);
  return out;
}

/* Whether the universal BOOLEAN, INTEGER or NULL at p, with max octets
   available, is one the library reads. */
static int typed_ok(int tag, const unsigned char *p, long max) {
  const unsigned char *q = p;
  int ok = 0;
  if (tag == V_ASN1_BOOLEAN) {
    ASN1_TYPE *t = d2i_ASN1_TYPE(NULL, &q, max);
    ok = t != NULL && ASN1_TYPE_get(t) == V_ASN1_BOOLEAN;
    ASN1_TYPE_free(t);
  } else if (tag == V_ASN1_INTEGER) {
    ASN1_INTEGER *i = d2i_ASN1_INTEGER(NULL, &q, max);
    ok = i != NULL;
    ASN1_INTEGER_free(i);
  } else if (tag == V_ASN1_NULL) {
    ASN1_NULL *z = d2i_ASN1_NULL(NULL, &q, max);
    ok = z != NULL;
    ASN1_NULL_free(z);
  } else {
    ok = 1;
  }
  ERR_clear_error();
  return ok;
}

/* An open constructed element: where its next element starts, where its
   contents end (for the indefinite length, where the octets around it
   end), whether its length is indefinite, and whether its next element
   is its first. */
typedef struct {
  const unsigned char *p, *end;
  int inf, first;
} frame_t;

/* Reads the element at *pp, with the octets up to end available, and
   writes the start of its tree. Moves *pp past a primitive element, or
   past the identifier and length octets of a constructed one, which is
   pushed. 0 when the library refuses it. */
static int one(const unsigned char **pp, const unsigned char *end, buf_t *out,
               frame_t **stack, size_t *depth, size_t *cap) {
  const unsigned char *p = *pp;
  long len;
  int tag, xclass, ret;
  char head[64];
  ret = ASN1_get_object(&p, &len, &tag, &xclass, (long) (end - *pp));
  ERR_clear_error();
  if (ret & 0x80) return 0;
  if (xclass == V_ASN1_UNIVERSAL && !typed_ok(tag, *pp, (long) (end - *pp))) return 0;
  if (ret & V_ASN1_CONSTRUCTED) {
    snprintf(head, sizeof head, "c%d.%d(", xclass >> 6, tag);
    puts_(out, head);
    if (*depth == *cap) {
      *cap = *cap ? 2 * *cap : 64;
      *stack = realloc(*stack, *cap * sizeof **stack);
      if (*stack == NULL) abort();
    }
    (*stack)[(*depth)++] = (frame_t) {p, (ret & 1) ? end : p + len, ret & 1, 1};
    *pp = p;
    return 1;
  }
  snprintf(head, sizeof head, "p%d.%d.", xclass >> 6, tag);
  puts_(out, head);
  put_hex(out, p, len);
  *pp = p + len;
  return 1;
}

/* The element at the start of the n octets at data, as a tree in out,
   and where the octets after it start in *rest. 0 when refused. */
static int element(const unsigned char *data, long n, buf_t *out, const unsigned char **rest) {
  static frame_t *stack = NULL;
  static size_t cap = 0;
  size_t depth = 0;
  const unsigned char *p = data, *end = data + n;
  if (n == 0) return 0;
  if (!one(&p, end, out, &stack, &depth, &cap)) return 0;
  /* After a constructed element is pushed, p is where its contents start;
     the frame holds its own position from then on. */
  while (depth > 0) {
    frame_t *f = &stack[depth - 1];
    int done;
    if (f->inf) {
      done = f->end - f->p >= 2 && f->p[0] == 0 && f->p[1] == 0;
      if (done) f->p += 2;
      else if (f->p == f->end) return 0;
    } else {
      done = f->p == f->end;
    }
    if (done) {
      const unsigned char *after = f->p;
      --depth;
      puts_(out, ")");
      if (depth > 0) stack[depth - 1].p = after;
      else p = after;
      continue;
    }
    if (!f->first) puts_(out, ",");
    f->first = 0;
    {
      const unsigned char *q = f->p, *limit = f->end;
      size_t before = depth;
      if (!one(&q, limit, out, &stack, &depth, &cap)) return 0;
      f = &stack[before - 1];
      if (depth == before) f->p = q;
    }
  }
  *rest = p;
  return 1;
}

static void der_length(buf_t *b, long n) {
  unsigned char octs[16];
  int k = 0;
  if (n < 128) {
    unsigned char c = (unsigned char) n;
    put(b, (char *) &c, 1);
    return;
  }
  for (long m = n; m > 0; m >>= 8) octs[k++] = (unsigned char) (m & 0xff);
  {
    unsigned char c = (unsigned char) (0x80 | k);
    put(b, (char *) &c, 1);
  }
  while (k > 0) put(b, (char *) &octs[--k], 1);
}

static void readint(const unsigned char *c, long n, buf_t *out) {
  buf_t framed = {0};
  const unsigned char *p;
  ASN1_INTEGER *i;
  put(&framed, "\x02", 1);
  der_length(&framed, n);
  put(&framed, (const char *) c, (size_t) n);
  p = (const unsigned char *) framed.s;
  i = d2i_ASN1_INTEGER(NULL, &p, (long) framed.n);
  if (i == NULL || p != (const unsigned char *) framed.s + framed.n) {
    puts_(out, "FAIL");
  } else {
    BIGNUM *bn = ASN1_INTEGER_to_BN(i, NULL);
    char *dec = bn ? BN_bn2dec(bn) : NULL;
    if (dec) {
      puts_(out, "OK ");
      puts_(out, dec);
    } else {
      puts_(out, "unreadable");
    }
    OPENSSL_free(dec);
    BN_free(bn);
  }
  ASN1_INTEGER_free(i);
  ERR_clear_error();
  free(framed.s);
}

static void writeint(const char *f, buf_t *out) {
  const char *digits = f[0] == '-' ? f + 1 : f;
  BIGNUM *bn = NULL;
  ASN1_INTEGER *i = NULL;
  unsigned char *der = NULL;
  int n;
  if (*digits == 0 || strspn(digits, "0123456789") != strlen(digits)) {
    puts_(out, "error");
    return;
  }
  if (BN_dec2bn(&bn, f) != (int) strlen(f) || (i = BN_to_ASN1_INTEGER(bn, NULL)) == NULL ||
      (n = i2d_ASN1_INTEGER(i, &der)) <= 0) {
    puts_(out, "FAIL");
  } else {
    const unsigned char *p = der;
    long len;
    int tag, xclass;
    int ret = ASN1_get_object(&p, &len, &tag, &xclass, n);
    if ((ret & 0x80) || p + len != der + n) {
      puts_(out, "unreadable");
    } else {
      puts_(out, "OK ");
      put_hex(out, p, len);
    }
  }
  OPENSSL_free(der);
  ASN1_INTEGER_free(i);
  BN_free(bn);
  ERR_clear_error();
}

static void answer(char *line, buf_t *out) {
  char *sp = strchr(line, ' ');
  char *op = line, *f;
  if (strcmp(line, "version") == 0) {
    puts_(out, "OK ");
    puts_(out, OpenSSL_version(OPENSSL_VERSION));
    return;
  }
  if (sp == NULL || strchr(sp + 1, ' ') != NULL) {
    puts_(out, "error");
    return;
  }
  *sp = 0;
  f = sp + 1;
  if (strcmp(op, "decode") == 0 || strcmp(op, "all") == 0 || strcmp(op, "readint") == 0) {
    long n;
    unsigned char *b = field(f, &n);
    if (b == NULL) {
      puts_(out, "error");
      return;
    }
    if (strcmp(op, "readint") == 0) {
      readint(b, n, out);
    } else {
      buf_t tree = {0};
      const unsigned char *rest = NULL;
      if (!element(b, n, &tree, &rest) || (strcmp(op, "all") == 0 && rest != b + n)) {
        puts_(out, "FAIL");
      } else {
        puts_(out, "OK ");
        put(out, tree.s, tree.n);
        if (strcmp(op, "decode") == 0) {
          puts_(out, " ");
          put_hex(out, rest, (long) (b + n - rest));
        }
      }
      free(tree.s);
    }
    free(b);
  } else if (strcmp(op, "writeint") == 0) {
    writeint(f, out);
  } else if (strcmp(op, "encode") == 0 || strcmp(op, "valid") == 0) {
    puts_(out, "n/a");
  } else {
    puts_(out, "error");
  }
}

int main(void) {
  char *line = NULL;
  size_t cap = 0;
  ssize_t got;
  buf_t out = {0};
  while ((got = getline(&line, &cap, stdin)) > 0) {
    if (line[got - 1] == '\n') line[--got] = 0;
    if (got > 0 && line[got - 1] == '\r') line[--got] = 0;
    out.n = 0;
    answer(line, &out);
    put(&out, "\n", 1);
    fwrite(out.s, 1, out.n, stdout);
  }
  free(line);
  free(out.s);
  return 0;
}
