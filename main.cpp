#define CIGINT_IMPLEMENTATION
#define CIGINT_STRIP_PREFIX
#define CIGINT_N (512 / 32)
#include "cigint.h"
#include <iostream>

static inline int is_space_c(unsigned char c) {
	return c==' '||c=='\t'||c=='\n'||c=='\r'||c=='\f'||c=='\v';
}
static inline int hex_val(unsigned char c) {
	if (c >= '0' && c <= '9') return (int)(c - '0');
	if (c >= 'a' && c <= 'f') return 10 + (int)(c - 'a');
	if (c >= 'A' && c <= 'F') return 10 + (int)(c - 'A');
	return -1;
}

Cigint cigint_from_dec(const char *s) {
	assert(s && "cigint_from_dec: null pointer");
	Cigint out = CIGINT_ZERO();

	// skip leading spaces and optional '+'
	while (is_space_c(*s)) ++s;
	if (*s == '+') ++s;
	assert(*s != '-' && "cigint_from_dec: negative not supported");

	// skip leading zeros, underscores, spaces
	const char *p = s;
	bool any = false;
	while (*p == '0' || *p == '_' || is_space_c(*p)) {
		if (*p == '0') any = true;
		++p;
	}

	for (; *p; ++p) {
		auto c = *p;
		if (c == '_' || is_space_c(c)) continue;
		if (c < '0' || c > '9') break;
		any = true;
		out = cigint_mul(out, 10u);
		out = cigint_add(out, (uint)(c - '0'));
	}

	// trailing junk? allow only spaces/underscores
	while (*p && (is_space_c(*p) || *p == '_')) ++p;
	assert(any && "cigint_from_dec: no digits");
	return out;
}

Cigint cigint_from_hex(const char *s) {
	assert(s && "cigint_from_hex: null pointer");
	Cigint out = CIGINT_ZERO();

	while (is_space_c(*s)) ++s;
	if (*s == '+') ++s;
	assert(*s != '-' && "cigint_from_hex: negative not supported");

	if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) s += 2;

	const char *p = s;
	bool any = false;

	// skip leading zeros/sep
	while (*p == '0' || *p == '_' || is_space_c(*p)) {
		if (*p == '0') any = true;
		++p;
	}

	for (; *p; ++p) {
		auto c = *p;
		if (c == '_' || is_space_c(c)) continue;
		int d = hex_val(c);
		if (d < 0) break;
		any = true;
		out = cigint_mul(out, 16u);
		out = cigint_add(out, (uint)d);
	}
	while (*p && (is_space_c(*p) || *p == '_')) ++p;
	assert(any && "cigint_from_hex: no digits");
	return out;
}

/* ---------- BINARY: multiply-by-2 then add bit (accepts optional 0b/0B) ---------- */

/* --- Implementations (put under #ifdef CIGINT_IMPLEMENTATION) --- */
/* Portable per-word bit reverse (no intrinsics, works for any 8k-bit uint) */
static uint u1_bitreverse(uint x) {
	uint r = 0;
	for (uint i = 0; i < SIZEOF_UINT; ++i) {
		r = (r << 1) | (x & 1u);
		x >>= 1;
	}
	return r;
}

/* Reverse all bits across the fixed width W = CIGINT_N * SIZEOF_UINT.
   Done by reversing limb order and reversing bits within each limb. */
Cigint cigint_bitreverse(Cigint& a) {
	Cigint r = CIGINT_ZERO();
	for (size_t i = 0; i < CIGINT_N; ++i) {
		r.data[i] = u1_bitreverse(a.data[CIGINT_N - 1 - i]);
	}
	return r;
}

/* Reverse only the lowest n bits (n may be < total width).
   For "1011 -> 1101", call with n = cigint_highest_order(a). */
Cigint cigint_bitreverse_n(Cigint& a, uint n) {
	Cigint r = CIGINT_ZERO();
	if (n == 0) return r;
	for (uint i = 0; i < n; ++i) {
		r = cigint_set_bit(r, n - 1 - i, cigint_get_bit(a, i));
	}
	return r;
}

Cigint cigint_from_bin(const char *s) {
	assert(s && "cigint_from_bin: null pointer");
	Cigint out = CIGINT_ZERO();

	while (is_space_c(*s)) ++s;
	if (s[0] == '0' && (s[1] == 'b' || s[1] == 'B')) s += 2;
	while (*s == '0' || *s == '_' || is_space_c(*s)) ++s;
	const char *p = s;
	size_t k = 0;
	printf("Num: ");
	for (; *p; ++p) {
		char c = *p;
		if (c == '_' || is_space_c(c)) continue;
		if (c != '0' && c != '1') break;
		printf("%c", c);
		++k;
	}
	printf("\n");
	assert(k && "cigint_from_bin: no digits");
	for (; *s; ++s) {
		char c = *s;
		if (c == '_' || is_space_c(c)) continue;
		if (c != '0' && c != '1') break;
		cigint_set_bit_ref(&out, --k, c == '1');
	}
	return out;
}

Cigint cigint_from_bin2(const char *s) {
	assert(s && "cigint_from_bin: null pointer");
	Cigint out = CIGINT_ZERO();

	while (is_space_c(*s)) ++s;
	if (s[0] == '0' && (s[1] == 'b' || s[1] == 'B')) s += 2;
	const char *p = s;
	while (*p == '0' || *p == '_' || is_space_c(*p)) ++p;
	size_t k = 0;
	printf("Num: ");
	for (; *p; ++p) {
		char c = *p;
		if (c == '_' || is_space_c(c)) continue;
		if (c != '0' && c != '1') break;
		printf("%c", c);
		cigint_set_bit_ref(&out, k++, c == '1');
	}
	printf("\n");
	assert(k && "cigint_from_bin: no digits");
	return cigint_bitreverse_n(out, k);
}

/* ---------- Autodetect: 0x.. => hex, 0b.. => bin, else dec ---------- */

Cigint cigint_from_str(const char *s) {
  assert(s && "cigint_from_str: null pointer");

  // skip spaces and '+'
  const char *p = s;
  while (is_space_c(*p)) ++p;
  if (*p == '+') ++p;
  if (*p == '-') {
    assert(0 && "cigint_from_str: negative not supported");
  }

  if (p[0] == '0' && (p[1] == 'x' || p[1] == 'X')) return cigint_from_hex(p);
  if (p[0] == '0' && (p[1] == 'b' || p[1] == 'B')) return cigint_from_bin(p);
  return cigint_from_dec(p);
}

/* Optional short aliases if you use CIGINT_STRIP_PREFIX like the rest */
#if defined(CIGINT_STRIP_PREFIX)
  #define from_dec  cigint_from_dec
  #define from_hex  cigint_from_hex
  #define from_bin  cigint_from_bin
  #define from_str  cigint_from_str
#endif

/* floor(sqrt(a)) via binary search: O(log n * M(n)) */
Cigint cigint_isqrt(FREF(Cigint) a) {
	/* 0,1 fast-path */
	if (cigint_is0(a)) return a;
	Cigint one = (Cigint){0}; one.data[CIGINT_N - 1] = 1;
	if (cigint_cmp(a, one) <= 0) return a;

	uint bits = cigint_highest_order(a);              /* 1.. */
	uint up   = (bits + 1u) / 2u;                     /* ceil(bits/2) */
	Cigint low = {0};
	Cigint high = cigint_pow2(up);                    /* 2^up */
	high = cigint_sub(high, one);                     /* 2^up - 1 */

	while (cigint_cmp(low, high) < 0) {
		/* mid = (low + high + 1) >> 1 */
		Cigint mid = cigint_add(low, high);
		mid = cigint_add(mid, one);
		mid = cigint_shr(mid, 1);

		Cigint mid2 = cigint_mul(mid, mid);
		if (cigint_cmp(mid2, a) <= 0) {
			low = mid;
		} else {
			high = cigint_sub(mid, one);
		}
	}
	return low;
}

Cigint cigint_isqrt3(Cigint& a) {
	if (cigint_is0(a)) return a;

	Cigint rem = a;                      // running remainder
	Cigint res = (Cigint){0};            // "trial root × 2"

	uint bits = cigint_highest_order(a);
	uint k = bits ? (bits - 1u) : 0u;    // top bit index
	if (k & 1u) k--;                     // make even → largest power of 4 ≤ a
	Cigint bit = cigint_pow2(k);         // starts at 4^⌊(bits-1)/2⌋

	while (!cigint_is0(bit)) {
		Cigint trial = cigint_add(res, bit);
		if (cigint_cmp(rem, trial) >= 0) {
			rem = cigint_sub(rem, trial);
			res = cigint_add(cigint_shr(res, 1), bit);
		} else {
			res = cigint_shr(res, 1);
		}
		bit = cigint_shr(bit, 2);
	}
	return res;
}

Cigint cigint_isqrt2(const Cigint& a) {
	return 1 << cigint_highest_order(a) / 2;
}

Cigint cigint_isqrt4(Cigint a) {
	if (cigint_is0(a)) return a;

	Cigint res = CIGINT_ZERO();            // “trial root × 2"
	uint bits = cigint_highest_order(a);
	uint k = bits ? (bits - 1u) : 0u;    // top bit index
	if (k & 1u) k--;                     // make even → largest power of 4 ≤ a
	Cigint bit = cigint_pow2(k);         // starts at 4^⌊(bits-1)/2⌋

	while (!cigint_is0(bit)) {
		Cigint trial = cigint_add(res, bit);
		if (cigint_cmp(a, trial) >= 0) {
			a = cigint_sub(a, trial);
			res = cigint_add(cigint_shr(res, 1), bit);
		} else {
			res = cigint_shr(res, 1);
		}
		bit = cigint_shr(bit, 2);
	}
	return res;
}

Cigint euclidean_gcd(Cigint a, Cigint b) {
	while (!cigint_is0(b)) {
		Cigint tmp = b;
		b = cigint_mod(a, b);
		a = tmp;
	}
	return a;
}

bool isPrime(const Cigint &n) {
	Cigint p = {2};
	if (cigint_cmp(n, p) < 0) return false;
	while (cigint_cmp(p * p, n) <= 0) {
		if (cigint_mod(n, p) == 0) return false;
		p = cigint_add(p, 1);
	}
	return true;
}

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wnon-pod-varargs"
int main() {
	Cigint tmp = {0};
	// tmp = cigint_from_dec("000001000A11");
	// cprintf("TMP: %Cd\n", tmp);
	// tmp = cigint_from_str("12345678901234567890");
	// cprintf("TMP: %Cd\n", tmp);
	// tmp = cigint_from_str("0xdead_beef_012345");
	// cprintf("TMP: %Cd\n", tmp);
	tmp = cigint_from_str("0b1010_1111_0001");
	cprintf("Dec: %Cd\n", tmp);
	cprintf("Bin: %Cb\n", tmp);
	while (cigint_cmp(tmp, 0) > 0) {
		tmp = cigint_shr(tmp, 1);
		cprintf("Dec: %Cd\n", tmp);
		cprintf("Bin: %Cb\n", tmp);
	}
	tmp = 1;
	tmp = cigint_shl(tmp, 1);
	cprintf("Dec: %Cd\n", tmp);
	cprintf("Bin: %Cb\n", tmp);
	tmp -= 1;
	cprintf("Dec: %Cd\n", tmp);
	cprintf("Bin: %Cb\n", tmp);
	tmp -= 1;
	cprintf("Dec: %Cd\n", tmp);
	cprintf("Bin: %Cb\n", tmp);
	tmp -= 1;
	cprintf("Dec: %Cd\n", tmp);
	cprintf("Bin: %Cb\n", tmp);
	// tmp = cigint_from_str("  42_000  ");
	// cprintf("TMP: %Cd\n", tmp);
	// tmp.data[CIGINT_N - 1] = (1ul << 31);
	// tmp = 2;
	// Cigint res1 = cigint_isqrt(tmp);
	// Cigint res2 = cigint_isqrt2(tmp);
	// Cigint res3 = cigint_isqrt3(tmp);
	// Cigint res4 = cigint_isqrt4(tmp);
	// cprintf("ISQRT1 of %Cd: %Cd\n", tmp, res1);
	// cprintf("ISQRT2 of %Cd: %Cd\n", tmp, res2);
	// cprintf("ISQRT2 of %Cd: %Cd\n", tmp, res3);
	// cprintf("ISQRT2 of %Cd: %Cd\n", tmp, res4);
	// cprintf("%Cb\n", tmp);
	// cprintf("%Cb\n", res1);
	// cprintf("%Cb\n", res2);
	// cprintf("%Cb\n", res3);
	// cprintf("%Cb\n", res4);
	return 0;
}
#pragma clang diagnostic pop