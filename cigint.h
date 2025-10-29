#ifndef CIGINT_H
#define CIGINT_H

#ifdef __cplusplus
#include <cassert>
#include <cstdio>
#include <cstdarg>
#include <cstring>
#include <cstdint>
#else
#include <assert.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <stdint.h>
#endif

#ifndef CIGINT_N
	#define CIGINT_N 8
#endif

#ifdef __cplusplus
	#define sassert static_assert
#else
	#define sassert _Static_assert
#endif
sassert(CIGINT_N > 1, "CIGINT_N > 1");

typedef uint32_t uint;
#define SIZEOF_UINT (8 * sizeof(uint))

typedef struct Cigint {
	uint data[CIGINT_N]{};

#ifdef __cplusplus
	Cigint() {
		memset(this->data, 0, sizeof(this->data));
	}
	Cigint(const Cigint &rhs) {
		memcpy(this->data, rhs.data, sizeof(rhs.data));
	}
	Cigint &operator=(const Cigint &rhs) {
		if (this != &rhs) {
			memcpy(this->data, rhs.data, sizeof(rhs.data));
		}
		return *this;
	}
	Cigint(uint rhs) {
		memset(this->data, 0, sizeof(this->data));
		this->data[CIGINT_N - 1] = rhs;
	}
#endif
} Cigint;

#ifdef __cplusplus
#define CIGINT_ZERO() Cigint{}
#else
#define CIGINT_ZERO() (Cigint){0}
#endif

#ifdef __cplusplus
#define FREF(type) type&
#else
#define FREF(type) type
#endif
uint cigint_get_bit(FREF(Cigint) a, uint pos);
Cigint cigint_set_bit(Cigint a, uint pos, uint val);
uint cigint_print10(FREF(Cigint) a);
uint cigint_print2(FREF(Cigint) a);
uint cigint_print16(FREF(Cigint) a);
uint cigint_print16_upper(FREF(Cigint) a);
int cigint_is0(FREF(Cigint) a);
int cigint_cmp(const FREF(Cigint) lhs, const FREF(Cigint) rhs);
uint cigint_highest_order(const FREF(Cigint) num);

inline void cigint_and_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_and(Cigint lhs, const FREF(Cigint) rhs);
void cigint_not_ref(Cigint *a);
Cigint cigint_not(Cigint a);
void cigint_xor_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_xor(Cigint lhs, const FREF(Cigint) rhs);
void cigint_or(Cigint *lhs, Cigint *rhs);
Cigint cigint_or_copy(Cigint lhs, FREF(Cigint) rhs);

Cigint cigint_shl(Cigint lhs, uint amnt);
Cigint cigint_shr(Cigint lhs, uint amnt);
Cigint cigint_pow2(uint amnt);

static inline void cigint_add_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_add(Cigint lhs, const FREF(Cigint) rhs);
static inline void cigint_sub_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_sub(Cigint lhs, const FREF(Cigint) rhs);
static inline void cigint_mul_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_mul(Cigint lhs, const FREF(Cigint) rhs);
static inline void cigint_sqr_ref(Cigint *base);
Cigint cigint_sqr(FREF(Cigint) base);
static inline void cigint_pow_ref(Cigint *base, uint exp);
Cigint cigint_pow(Cigint base, uint exp);

Cigint cigint_pow(Cigint lhs, uint amnt);
Cigint cigint_div(Cigint lhs, Cigint rhs);
Cigint cigint_mod(Cigint lhs, Cigint rhs);
void cigint_divmod(Cigint lhs, Cigint rhs, Cigint *q, Cigint *r);
uint cigint_printf(const char *fmt, ...);

#ifdef CIGINT_STRIP_PREFIX
	#define get_bit_ref cigint_get_bit_ref
	#define get_bit cigint_get_bit
	#define set_bit cigint_set_bit

	/* not to be confused with C++ macros */
	#define cand cigint_and
	#define cor cigint_or
	#define cxor cigint_xor
	#define cnot cigint_not

	#define shl cigint_shl
	#define shr cigint_shr
	#define highest_order cigint_highest_order
	#define pow2 cigint_pow2
	#define cmp cigint_cmp
	#define is0 cigint_is0

	#define add cigint_add
	#define addr cigint_add_ref
	#define sub cigint_sub
	#define subr cigint_sub_ref
	#define mul cigint_mul
	#define mulr cigint_mul_ref

	#define pow cigint_pow
	#define div cigint_div
	#define mod cigint_mod
	#define divmod cigint_divmod

	#define print2 cigint_print2
	#define print10 cigint_print10
	#define print16 cigint_print16
	#define print16U cigint_print16_upper
	#define cprintf cigint_printf
#endif

#ifdef CIGINT_IMPLEMENTATION
static uint u1_get_bit(uint num, uint pos) { return (num >> pos) & (uint)1; }

static uint u1_set_bit(uint num, uint pos, uint val) {
	if (pos >= SIZEOF_UINT) return num;
	uint mask = (uint)1 << pos;
	uint bit  = (val & 1u) ? mask : 0u;
	return (num & ~mask) | bit;
}

static uint u1_highest_order(uint num) {
	uint pos = 0;
	while (num > 0) {
		pos++;
		num >>= 1;
	}
	return pos;
}

static uint u1_get_last_nbits(uint num, uint amnt) {
	if (amnt >= SIZEOF_UINT) {
		return 0;
	}
	return num & ((1ul << amnt) - 1);
}

static uint cigint_get_bit_ref(Cigint *a, uint pos) {
	size_t data_index = CIGINT_N - 1 - pos / SIZEOF_UINT;
	return u1_get_bit(a->data[data_index], pos % SIZEOF_UINT);
}

static Cigint *cigint_set_bit_ref(Cigint *a, uint pos, uint val) {
	assert(pos < CIGINT_N * SIZEOF_UINT);
	size_t data_index = CIGINT_N - 1 - pos / SIZEOF_UINT;
	a->data[data_index] = u1_set_bit(a->data[data_index], pos % SIZEOF_UINT, val);
	return a;
}

inline uint cigint_get_bit(FREF(Cigint) a, uint pos) {
	return cigint_get_bit_ref(&a, pos);
}

inline Cigint cigint_set_bit(Cigint a, uint pos, uint val) {
	return *cigint_set_bit_ref(&a, pos, val);
}

// TODO: Write doc
inline void cigint_and_ref(Cigint *lhs, const Cigint *rhs) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		lhs->data[i] &= rhs->data[i];
	}
}

// TODO: Write doc
Cigint cigint_and(Cigint lhs, const FREF(Cigint) rhs) {
	cigint_and_ref(&lhs , &rhs);
	return lhs;
}

/**
 * @brief Performs a bitwise OR operation (lhs |= rhs) between two Cigint values.
 * @param lhs Pointer to the left-hand operand; stores the result.
 * @param rhs Pointer to the right-hand operand.
 */
void cigint_or_ref(Cigint *lhs, const Cigint *rhs) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		lhs->data[i] |= rhs->data[i];
	}
}

/**
 * @brief Returns the bitwise OR (r = lhs | rhs) of two Cigint values.
 * This is a copy wrapper of ::cigint_or()
 * @param lhs Left-hand operand (copied before modification).
 * @param rhs Right-hand operand.
 */
Cigint cigint_or(Cigint lhs, const FREF(Cigint) rhs) {
	cigint_or_ref(&lhs, &rhs);
	return lhs;
}

// TODO: Write doc
void cigint_not_ref(Cigint *a) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		a->data[i] = ~a->data[i];
	}
}

// TODO: Write doc
Cigint cigint_not(Cigint a) {
	cigint_not_ref(&a);
	return a;
}

/**
 * @brief Performs a bitwise XOR operation (lhs ^= rhs) between two Cigint values.
 * @param lhs Pointer to the left-hand operand; stores the result.
 * @param rhs Pointer to the right-hand operand.
 */
void cigint_xor_ref(Cigint *lhs, const Cigint *rhs) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		lhs->data[i] ^= rhs->data[i];
	}
}

/**
 * @brief Returns the bitwise XOR (r = lhs ^ rhs) of two Cigint values.
 * This is a copy wrapper of ::cigint_xor()
 * @param lhs Left-hand operand (copied before modification).
 * @param rhs Right-hand operand.
 */
Cigint cigint_xor(Cigint lhs, const FREF(Cigint) rhs) {
	cigint_xor_ref(&lhs, &rhs);
	return lhs;
}

/* Two-phase, MSW-first left shift: limb move plus intra-word stitch. */
Cigint cigint_shl(Cigint lhs, uint amnt) {
	if (amnt == 0) return lhs;

	const size_t limb_off = amnt / SIZEOF_UINT;
	const uint bits = amnt % SIZEOF_UINT;

	if (limb_off >= CIGINT_N) return CIGINT_ZERO(); // everything shifted out
	Cigint r = (Cigint){0};
	// Phase 1: limb-only move (toward MSW)
	for (size_t i = 0; i + limb_off < CIGINT_N; ++i)
		r.data[i] = lhs.data[i + limb_off];
	// Phase 2: intra-word stitch (only if bits != 0)
	if (bits) {
		uint snapshot[CIGINT_N];
		// for (size_t i = 0; i < CIGINT_N; ++i) snapshot[i] = r.data[i];
		memcpy(snapshot, r.data, sizeof snapshot);
		for (size_t i = 0; i < CIGINT_N; ++i) {
			const uint hi = snapshot[i] << bits;
			const uint lo = i + 1 < CIGINT_N ? snapshot[i + 1] >> (SIZEOF_UINT - bits) : 0u;
			r.data[i] = hi | lo;
		}
	}
	return r;
}

/* Two-phase, MSW-first right shift: limb move plus intra-word stitch */
Cigint cigint_shr(Cigint lhs, uint amnt) {
	if (amnt == 0) return lhs;
	const size_t limb_off = amnt / SIZEOF_UINT;
	const uint bits = amnt % SIZEOF_UINT;
	if (limb_off >= CIGINT_N) return CIGINT_ZERO(); // everything shifted out
	Cigint r = CIGINT_ZERO();
	// Phase 1: limb-only move (toward LSW)
	for (size_t i = CIGINT_N; i-- > limb_off; )
		r.data[i] = lhs.data[i - limb_off];
	// Phase 2: intra-word stitch (only if bits != 0)
	if (bits) {
		uint snapshot[CIGINT_N];
		memcpy(snapshot, r.data, sizeof snapshot);
		for (size_t i = 0; i < CIGINT_N; ++i) {
			const uint lo = snapshot[i] >> bits;
			const uint hi = i > 0 ? snapshot[i - 1] << (SIZEOF_UINT - bits) : 0u;
			r.data[i] = hi | lo;
		}
	}
	return r;
}

uint cigint_highest_order(const FREF(Cigint) num) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		if (num.data[i] > 0) {
			return u1_highest_order(num.data[i]) + (CIGINT_N - i - 1) * SIZEOF_UINT;
		}
	}
	return 0;
}

Cigint cigint_pow2(uint amnt) {
	assert(amnt < CIGINT_N * SIZEOF_UINT);
	Cigint r = CIGINT_ZERO();
	size_t limb = CIGINT_N - 1 - (amnt / SIZEOF_UINT);
	r.data[limb] = (uint)(1u << (amnt % SIZEOF_UINT));
	return r;
}

int cigint_cmp(const FREF(Cigint) lhs, const FREF(Cigint) rhs) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		if (lhs.data[i] != rhs.data[i]) {
			return lhs.data[i] > rhs.data[i] ? 1 : -1;
		}
	}
	return 0;
}

int cigint_is0(FREF(Cigint) a) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		if (a.data[i] != 0) {
			return 0;
		}
	}
	return 1;
}

static inline void cigint_add_ref(Cigint *lhs, const Cigint *rhs) {
	uint64_t sum = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		sum = (uint64_t) lhs->data[i] + (uint64_t) rhs->data[i] + (sum >> SIZEOF_UINT);
		lhs->data[i] = (uint) sum;
	}
}

Cigint cigint_add(Cigint lhs, const FREF(Cigint) rhs) {
	cigint_add_ref(&lhs, &rhs);
	return lhs;
}

static inline void cigint_sub_ref(Cigint *lhs, const Cigint *rhs) {
	uint64_t borrow = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		uint64_t a = lhs->data[i];
		uint64_t t = (uint64_t)rhs->data[i] + borrow;
		lhs->data[i] = (uint32_t)(a - t);
		borrow = a < t;
	}
}

Cigint cigint_sub(Cigint lhs, const FREF(Cigint) rhs) {
	cigint_sub_ref(&lhs, &rhs);
	return lhs;
}

// void cigint_mul_ref(Cigint *a, const Cigint *b) {
// 	Cigint temp = CIGINT_ZERO();
// 	uint64_t carry = 0;
//
// 	// Compute LSW-first into temp
// 	for (size_t k = 0; k < CIGINT_N; ++k) {
// 		uint64_t acc = carry;
// 		for (size_t i = 0; i <= k; ++i) {
// 			acc += (uint64_t)a->data[CIGINT_N - 1 - i] * (uint64_t)b->data[CIGINT_N - 1 - (k - i)];
// 		}
// 		temp.data[k] = (uint32_t)acc;
// 		carry = acc >> 32;
// 	}
//
// 	// Copy temp back to a->data in MSW-first order
// 	for (size_t k = 0; k < CIGINT_N; ++k) {
// 		a->data[CIGINT_N - 1 - k] = temp.data[k];
// 	}
// }

static inline void cigint_mul_ref(Cigint *lhs, const Cigint *rhs) {
	Cigint tmp = CIGINT_ZERO();
	uint64_t carry = 0;

	for (size_t k = 0; k < CIGINT_N; ++k) {
		uint64_t acc = carry;
		for (size_t i = 0; i <= k; ++i) {
			acc += (uint64_t) lhs->data[CIGINT_N - 1 - i] * (uint64_t) rhs->data[CIGINT_N - 1 - (k - i)];
		}
		tmp.data[CIGINT_N - 1 - k] = (uint32_t) acc;
		carry = acc >> SIZEOF_UINT;
	}
	*lhs = tmp;
}

Cigint cigint_mul(Cigint lhs, const FREF(Cigint) rhs) {
	cigint_mul_ref(&lhs, &rhs);
	return lhs;
}

static inline void cigint_sqr_ref(Cigint *base) {
	Cigint tmp = CIGINT_ZERO();
	for (size_t i = 0; i < CIGINT_N; ++i) {
		for (size_t j = 0; j <= i; ++j) {
			uint64_t p = (uint64_t)base->data[i] * (uint64_t)base->data[j];
			if (i != j) p <<= 1; // double off-diagonal
			size_t k = i + j;
			if (k < CIGINT_N) {
				uint64_t sum = (uint64_t) tmp.data[k] + p;
				tmp.data[k] = (uint) sum; // ignore overflow beyond 32/64 bits of out[k]
			}
		}
	}
	*base = tmp;
}

Cigint cigint_sqr(FREF(Cigint) base) {
	cigint_sqr_ref(&base);
	return base;
}

static inline void cigint_pow_ref(Cigint *base, uint exp) {
	Cigint res = 1;
	while (exp) {
		if (exp & 1u) cigint_mul_ref(&res, base);
		exp >>= 1;
		if (!exp) break;
		cigint_sqr_ref(base);
	}
	*base = res;
}

Cigint cigint_pow(Cigint base, uint exp) {
	cigint_pow_ref(&base, exp);
	return base;
}

Cigint cigint_div(Cigint lhs, Cigint rhs) {
	assert(!cigint_is0(rhs));
	int comp = cigint_cmp(lhs, rhs);
	if (comp <= 0) {
		Cigint res = CIGINT_ZERO();
		res.data[CIGINT_N - 1] = comp == 0;
		return res;
	}
	Cigint quotient = CIGINT_ZERO(), r = quotient;
	int bit_index = cigint_highest_order(lhs) - 1;
	while (bit_index >= 0) {
		r = cigint_shl(r, 1);
		r = cigint_set_bit(r, 0, cigint_get_bit(lhs, bit_index));
		if (cigint_cmp(r, rhs) >= 0) {
			r = cigint_sub(r, rhs);
			quotient = cigint_set_bit(quotient, bit_index, 1);
		}
		bit_index--;
	}
	return quotient;
}

Cigint cigint_mod(Cigint lhs, Cigint rhs) {
	assert(!cigint_is0(rhs));
	int comp = cigint_cmp(lhs, rhs);
	if (comp < 0) return lhs;
	if (comp == 0) return CIGINT_ZERO();
	Cigint quotient = CIGINT_ZERO(), r = quotient;
	int bit_index = cigint_highest_order(lhs) - 1;
	while (bit_index >= 0) {
		r = cigint_shl(r, 1);
		r = cigint_set_bit(r, 0, cigint_get_bit(lhs, bit_index));
		if (cigint_cmp(r, rhs) >= 0) {
			r = cigint_sub(r, rhs);
			quotient = cigint_set_bit(quotient, bit_index, 1);
		}
		bit_index--;
	}
	return r;
}

void cigint_divmod(Cigint lhs, Cigint rhs, Cigint *q, Cigint *r) {
	assert(!cigint_is0(rhs));
	int comp = cigint_cmp(lhs, rhs);
	if (comp <= 0) {
		if (q != NULL) {
			Cigint res = CIGINT_ZERO();
			res.data[CIGINT_N - 1] = comp == 0;
			*q = res;
		}
		if (r != NULL) {
			*r = (comp == 0) ? CIGINT_ZERO() : lhs;
		}
		return;
	}
	Cigint quotient = CIGINT_ZERO(), remainder = quotient;
	int bit_index = cigint_highest_order(lhs) - 1;
	while (bit_index >= 0) {
		remainder = cigint_shl(remainder, 1);
		remainder = cigint_set_bit(remainder, 0, cigint_get_bit(lhs, bit_index));
		if (cigint_cmp(remainder, rhs) >= 0) {
			remainder = cigint_sub(remainder, rhs);
			quotient = set_bit(quotient, bit_index, 1);
		}
		bit_index--;
	}
	if (q != NULL) {
		*q = quotient;
	}
	if (r != NULL) {
		*r = remainder;
	}
}

void cigint_sdivmod(Cigint lhs, uint rhs, Cigint *q, uint *r) {
	assert(rhs != 0);
	uint hord = cigint_highest_order(lhs);
	if (hord < SIZEOF_UINT && lhs.data[CIGINT_N - 1] <= rhs) {
		if (q != NULL) {
			Cigint res = CIGINT_ZERO();
			res.data[CIGINT_N - 1] = lhs.data[CIGINT_N - 1] == rhs;
			*q = res;
		}
		if (r != NULL) {
			*r = lhs.data[CIGINT_N - 1];
		}
		return;
	}
	Cigint quotient = CIGINT_ZERO();
	uint remainder = 0;
	int bit_index = hord - 1;
	while (bit_index >= 0) {
		remainder = remainder << 1;
		remainder = u1_set_bit(remainder, 0, cigint_get_bit(lhs, bit_index));
		if (remainder >= rhs) {
			remainder -= rhs;
			quotient = cigint_set_bit(quotient, bit_index, 1);
		}
		bit_index--;
	}
	if (q != NULL) {
		*q = quotient;
	}
	if (r != NULL) {
		*r = remainder;
	}
}



uint cigint_print2(FREF(Cigint) a) {
	uint counter = printf("0b"), old_counter = counter;
	int bit_index = cigint_highest_order(a) - 1;

	while (bit_index >= 0) {
		/* TODO: use %2 */
		int digit = cigint_get_bit_ref(&a, bit_index);
		counter += printf("%d", digit);
		bit_index--;
	}
	if (counter == old_counter) {
		counter += putchar('0');
	}
	return counter;
}

// Each Cigint has CIGINT_N * 32 bits.
// Each 10^8 chunk holds ~26.6 bits (log2(10^8) ≈ 26.6). So max chunks = ceil(total_bits / 26.6)
#define CIGINT_PRINT10_CHUNKS ((CIGINT_N * SIZEOF_UINT + 26) / 27)
uint cigint_print10(FREF(Cigint) a) {
	if (cigint_is0(a)) {
		putchar('0');
		return 1;
	}
	uint remainders[CIGINT_PRINT10_CHUNKS];
	size_t count = 0;
	Cigint q, n = a;
	while (!cigint_is0(n)) {
		uint r;
		cigint_sdivmod(n, 100000000U, &q, &r);
		remainders[count++] = r;
		n = q;
	}

	uint counter = 0;
	counter += printf("%u", remainders[count - 1]);
	for (size_t i = count - 1; i-- > 0;) {
		counter += printf("%08u", remainders[i]);
	}
	return counter;
}

static uint cigint_print16_impl(FREF(Cigint) a, int upper) {
	uint counter = 0;
	counter += printf("0x");
	size_t i = 0;
	while (i < CIGINT_N && a.data[i] == 0u) ++i;
	if (i == CIGINT_N) {
		counter += putchar('0');
		return counter;
	}
	counter += printf(upper ? "%X" : "%x", a.data[i]);
	for (size_t j = i + 1; j < CIGINT_N; ++j) {
		counter += printf(upper ? "%08X" : "%08x", a.data[j]);
	}
	return counter;
}

uint cigint_print16(FREF(Cigint) a)       { return cigint_print16_impl(a, 0); }
uint cigint_print16_upper(FREF(Cigint) a) { return cigint_print16_impl(a, 1); }

uint cigint_printf(const char *fmt, ...) {
	uint counter = 0;
	va_list lst;
	va_start(lst, fmt);
	while (*fmt != '\0') {
		switch (*fmt) {
			case '%': {
				fmt++;
				if (*fmt == '%') {
					putchar('%');
					counter++;
				} else if (*fmt == 'C') {
					char next = *(fmt + 1);
					if (next == 'b' || next == 'd' || next == 'x' || next == 'X') {
						fmt++;
						Cigint num = va_arg(lst, Cigint);
						if (*fmt == 'b')      counter += cigint_print2(num);
						else if (*fmt == 'd') counter += cigint_print10(num);
						else if (*fmt == 'x') counter += cigint_print16(num);
						else                  counter += cigint_print16_upper(num); /* 'X' */
					}
				} else if (*fmt == 'c') {
					int ch = va_arg(lst, int);
					counter += putchar(ch);
				} else if (*fmt == 'd' || *fmt == 'i') {
					int num = va_arg(lst, int);
					counter += printf("%d", num);
				} else if (*fmt == 's') {
					char *str = (char*) va_arg(lst, char*);
					counter += printf("%s", str);
				}
				break;
			}
			default: {
				counter += putchar(*fmt);
			}
		}
		fmt++;
	}

	va_end(lst);
	return counter;
}
#endif

#ifdef __cplusplus
inline Cigint operator+(const Cigint &lhs, const Cigint &rhs) {
	return cigint_add(lhs, rhs);
}

inline const Cigint &operator+=(Cigint &lhs, const Cigint &rhs) {
	cigint_add_ref(&lhs, &rhs);
	return lhs;
}

/* TODO: find an ideal way when calculate with u32 */
inline Cigint operator+(const Cigint &lhs, uint rhs) {
	return cigint_add(lhs, (Cigint) rhs);
}

inline const Cigint &operator+=(Cigint &lhs, uint rhs) {
	Cigint tmp = rhs;
	cigint_add_ref(&lhs, &tmp);
	return lhs;
}

inline Cigint operator-(const Cigint &lhs, const Cigint &rhs) {
	return cigint_sub(lhs, rhs);
}

inline const Cigint &operator-=(Cigint &lhs, const Cigint &rhs) {
	lhs = cigint_sub(lhs, rhs);
	return lhs;
}

inline Cigint operator*(const Cigint &lhs, const Cigint &rhs) {
	return cigint_mul(lhs, rhs);
}

inline const Cigint &operator*=(Cigint &lhs, const Cigint &rhs) {
	lhs = cigint_mul(lhs, rhs);
	return lhs;
}

inline Cigint operator/(const Cigint &lhs, const Cigint &rhs) {
	return cigint_div(lhs, rhs);
}

inline const Cigint &operator/=(Cigint &lhs, const Cigint &rhs) {
	lhs = cigint_div(lhs, rhs);
	return lhs;
}

inline bool operator==(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) == 0;
}

inline bool operator!=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) != 0;
}

inline bool operator>(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) > 0;
}

inline bool operator<(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) < 0;
}

inline bool operator>=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) >= 0;
}

inline bool operator<=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) <= 0;
}
#endif
#endif