#include <assert.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

#ifndef CIGINT_N
	#define CIGINT_N 8
#endif

#ifdef __cplusplus
	#define sassert static_assert
#else
	#define sassert _Static_assert
#endif
sassert(CIGINT_N > 1, "CIGINT_N > 1");

typedef unsigned int uint;
#define SIZEOF_UINT (8 * sizeof(uint))

typedef struct Cigint {
	uint data[CIGINT_N];

#ifdef __cplusplus
	Cigint() {
		memset(this->data, 0, sizeof(this->data));
	}
	Cigint(const Cigint &rhs) {
		memcpy(this->data, rhs.data, sizeof(rhs.data));
	}
	Cigint &operator=(const Cigint &rhs) {
		memcpy(this->data, rhs.data, sizeof(rhs.data));
		return *this;
	}
	Cigint(uint rhs) {
		memset(this->data, 0, sizeof(this->data));
		this->data[CIGINT_N - 1] = rhs;
	}
#endif
} Cigint;

uint cigint_get_bit(Cigint a, uint pos);
Cigint cigint_set_bit(Cigint a, uint pos, uint val);
uint cigint_print2(Cigint a);
Cigint cigint_and(Cigint lhs, Cigint rhs);
Cigint cigint_or(Cigint lhs, Cigint rhs);
Cigint cigint_xor(Cigint lhs, Cigint rhs);
Cigint cigint_not(Cigint a);
Cigint cigint_shl(Cigint lhs, uint amnt);
Cigint cigint_shr(Cigint lhs, uint amnt);
uint cigint_highest_order(Cigint num);
Cigint cigint_pow2(uint amnt);
int cigint_cmp(Cigint lhs, Cigint rhs);
int cigint_is0(Cigint a);
Cigint cigint_add(Cigint lhs, Cigint rhs);
Cigint cigint_sub(Cigint lhs, Cigint rhs);
Cigint cigint_mul(Cigint lhs, Cigint rhs);
Cigint cigint_pow(Cigint lhs, uint amnt);
Cigint cigint_div(Cigint lhs, Cigint rhs);
Cigint cigint_mod(Cigint lhs, Cigint rhs);
void cigint_divmod(Cigint lhs, Cigint rhs, Cigint *q, Cigint *r);
uint cigint_print10(Cigint a);
uint cigint_printf(const char *fmt, ...);

#ifdef CIGINT_STRIP_PREFIX
	#define get_bit cigint_get_bit
	#define set_bit cigint_set_bit
	#define print2 cigint_print2

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
	#define sub cigint_sub
	#define mul cigint_mul
	#define pow cigint_pow
	#define div cigint_div
	#define mod cigint_mod
	#define divmod cigint_divmod
	#define print10 cigint_print10
	#define cprintf cigint_printf
#endif

#ifdef CIGINT_IMPLEMENTATION
static uint u1_get_bit(uint num, uint pos) {
	if (pos >= SIZEOF_UINT) {
		return 0;
	}

	return (num & (1UL << pos)) >> pos;
}

static uint u1_set_bit(uint num, uint pos, uint val) {
	if (pos >= SIZEOF_UINT) {
		return 0;
	}

	return (num & ~(1UL << pos)) | (val << pos);
}

static uint u1_shl(uint num, uint amnt) {
	if (amnt >= SIZEOF_UINT) {
		return 0;
	}

	return num << amnt;
}

static uint u1_shr(uint num, uint amnt) {
	if (amnt >= SIZEOF_UINT) {
		return 0;
	}

	return num >> amnt;
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

uint cigint_get_bit(Cigint a, uint pos) {
	size_t data_index = CIGINT_N - 1 - pos / SIZEOF_UINT;
	return u1_get_bit(a.data[data_index], pos % SIZEOF_UINT);
}

Cigint cigint_set_bit(Cigint a, uint pos, uint val) {
	size_t data_index = CIGINT_N - 1 - pos / SIZEOF_UINT;
	a.data[data_index] = u1_set_bit(a.data[data_index], pos % SIZEOF_UINT, val);
	return a;
}

uint cigint_print2(Cigint a) {
	uint counter = printf("0b"), old_counter = counter;
	int bit_index = highest_order(a) - 1;

	while (bit_index >= 0) {
		/* TODO: use %2 */
		int digit = get_bit(a, bit_index);
		counter += printf("%d", digit);
		bit_index--;
	}
	if (counter == old_counter) {
		counter += putchar('0');
	}
	return counter;
}

Cigint cigint_and(Cigint lhs, Cigint rhs) {
	size_t i = 0;
	while (i < CIGINT_N) {
		lhs.data[i] &= rhs.data[i];
		i++;
	}
	return lhs;
}

Cigint cigint_or(Cigint lhs, Cigint rhs) {
	size_t i = 0;
	while (i < CIGINT_N) {
		lhs.data[i] |= rhs.data[i];
		i++;
	}
	return lhs;
}

Cigint cigint_xor(Cigint lhs, Cigint rhs) {
	size_t i = 0;
	while (i < CIGINT_N) {
		lhs.data[i] ^= rhs.data[i];
		i++;
	}
	return lhs;
}

Cigint cigint_not(Cigint a) {
	size_t i = 0;
	while (i < CIGINT_N) {
		a.data[i] = ~a.data[i];
		i++;
	}
	return a;
}

Cigint cigint_shl(Cigint lhs, uint amnt) {
	Cigint res = lhs;
	size_t i = 0;
	size_t offset = (amnt + SIZEOF_UINT - 1) / SIZEOF_UINT;
	size_t rshift_amnt = SIZEOF_UINT - (amnt % SIZEOF_UINT);
	while (i < CIGINT_N - offset) {
		res.data[i] = u1_shl(lhs.data[i], amnt);
		res.data[i] |= u1_shr(lhs.data[i + offset], rshift_amnt);
		i++;
	}
	while (i < CIGINT_N) {
		res.data[i] = u1_shl(lhs.data[i], amnt);
		i++;
	}
	return res;
}

Cigint cigint_shr(Cigint lhs, uint amnt) {
	Cigint res = lhs;
	size_t i = 0;
	size_t offset = (amnt + SIZEOF_UINT - 1) / SIZEOF_UINT;
	size_t bits_amnt = amnt % SIZEOF_UINT;
	size_t lshift_amnt = SIZEOF_UINT - bits_amnt;
	while (i < CIGINT_N - offset) {
		res.data[CIGINT_N - 1 - i] = u1_shr(lhs.data[CIGINT_N - 1 - i], amnt);
		uint last_bits =
				u1_get_last_nbits(lhs.data[CIGINT_N - 1 - i - offset], bits_amnt);
		res.data[CIGINT_N - 1 - i] |= u1_shl(last_bits, lshift_amnt);
		i++;
	}
	while (i < CIGINT_N) {
		res.data[CIGINT_N - 1 - i] = u1_shr(lhs.data[CIGINT_N - 1 - i], amnt);
		i++;
	}
	return res;
}

uint cigint_highest_order(Cigint num) {
	size_t i = 0;
	while (i < CIGINT_N) {
		if (num.data[i] > 0) {
			return u1_highest_order(num.data[i]) + (CIGINT_N - i - 1) * SIZEOF_UINT;
		}
		i++;
	}
	return 0;
}

Cigint cigint_pow2(uint amnt) {
	assert(amnt < CIGINT_N * SIZEOF_UINT);
	Cigint res = {0};
	res.data[amnt / SIZEOF_UINT] = (1 << (amnt % SIZEOF_UINT));
	return res;
}

int cigint_cmp(Cigint lhs, Cigint rhs) {
	size_t i = 0;
	while (i < CIGINT_N) {
		if (lhs.data[i] != rhs.data[i]) {
			return lhs.data[i] > rhs.data[i] ? 1 : -1;
		}
		i++;
	}
	return 0;
}

int cigint_is0(Cigint a) {
	size_t i = 0;
	while (i < CIGINT_N) {
		if (a.data[i] != 0) {
			return 0;
		}
		i++;
	}
	return 1;
}

Cigint cigint_add(Cigint lhs, Cigint rhs) {
	while (!cigint_is0(rhs)) {
		Cigint carry = cigint_and(lhs, rhs);
		lhs = cigint_xor(lhs, rhs);
		rhs = cigint_shl(carry, 1);
	}
	return lhs;
}

Cigint cigint_sub(Cigint lhs, Cigint rhs) {
	while (!cigint_is0(rhs)) {
		Cigint borrow = cigint_and(cigint_not(lhs), rhs);
		lhs = cigint_xor(lhs, rhs);
		rhs = cigint_shl(borrow, 1);
	}
	return lhs;
}

Cigint cigint_mul(Cigint lhs, Cigint rhs) {
	Cigint res = {0};
	while (!cigint_is0(rhs)) {
		if (u1_get_bit(rhs.data[CIGINT_N - 1], 0) == 1) {
			res = cigint_add(res, lhs);
		}
		lhs = cigint_shl(lhs, 1);
		rhs = cigint_shr(rhs, 1);
	}
	return res;
}

Cigint cigint_pow(Cigint lhs, uint amnt) {
	Cigint res = {0};
	res.data[CIGINT_N - 1] = 1;
	while (amnt > 0) {
	if (amnt % 2 == 1) {
		res = mul(res, lhs);
	}

	lhs = mul(lhs, lhs);
	amnt /= 2;
	}
	return res;
}

Cigint cigint_div(Cigint lhs, Cigint rhs) {
	assert(!cigint_is0(rhs));
	int comp = cigint_cmp(lhs, rhs);
	if (comp <= 0) {
		Cigint res = {0};
		res.data[CIGINT_N - 1] = comp == 0;
		return res;
	}
	Cigint quotient = {0}, r = quotient;
	int bit_index = cigint_highest_order(lhs) - 1;
	while (bit_index >= 0) {
		r = cigint_shl(r, 1);
		r = set_bit(r, 0, get_bit(lhs, bit_index));
		if (cigint_cmp(r, rhs) >= 0) {
			r = cigint_sub(r, rhs);
			quotient = set_bit(quotient, bit_index, 1);
		}
		bit_index--;
	}
	return quotient;
}

Cigint cigint_mod(Cigint lhs, Cigint rhs) {
	assert(!cigint_is0(rhs));
	int comp = cigint_cmp(lhs, rhs);
	if (comp <= 0) {
		return lhs;
	}
	Cigint quotient = {0}, r = quotient;
	int bit_index = cigint_highest_order(lhs) - 1;
	while (bit_index >= 0) {
		r = cigint_shl(r, 1);
		r = set_bit(r, 0, get_bit(lhs, bit_index));
		if (cigint_cmp(r, rhs) >= 0) {
			r = cigint_sub(r, rhs);
			quotient = set_bit(quotient, bit_index, 1);
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
			Cigint res = {0};
			res.data[CIGINT_N - 1] = comp == 0;
			*q = res;
		}
		if (r != NULL) {
			*r = lhs;
		}
		return;
	}
	Cigint quotient = {0}, remainder = quotient;
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
			Cigint res = {0};
			res.data[CIGINT_N - 1] = lhs.data[CIGINT_N - 1] == rhs;
			*q = res;
		}
		if (r != NULL) {
			*r = lhs.data[CIGINT_N - 1];
		}
		return;
	}
	Cigint quotient = {0};
	uint remainder = 0;
	int bit_index = hord - 1;
	while (bit_index >= 0) {
		remainder = remainder << 1;
		remainder = u1_set_bit(remainder, 0, cigint_get_bit(lhs, bit_index));
		if (remainder >= rhs) {
			remainder -= rhs;
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

/* TODO: stack overflow */
uint cigint_print10(Cigint a) {
	if (cigint_is0(a)) {
		return 0;
	}

	Cigint q;
	uint r;
	cigint_sdivmod(a, 100000000, &q, &r);

	uint counter = cigint_print10(q);
	if (counter == 0) {
		counter += printf("%u", r);
	}
	else {
		counter += printf("%0*u", 8, r);
	}
	return counter;
}

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
				}
				else if (*fmt == 'C') {
					if (*(fmt + 1) == 'b' || *(fmt + 1) == 'd') {
						fmt++;
						Cigint num = (Cigint) va_arg(lst, Cigint);
						if (*fmt == 'b') {
							counter += cigint_print2(num);
						}
						else {
							counter += cigint_print10(num);
						}
					}
				}
				else if (*fmt == 'c') {
					int ch = va_arg(lst, int);
					counter += putchar(ch);
				}
				else if (*fmt == 'd' || *fmt == 'i') {
					int num = va_arg(lst, int);
					counter += printf("%d", num);
				}
				else if (*fmt == 's') {
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
	lhs = cigint_add(lhs, rhs);
	return lhs;
}

/* TODO: find an ideal way when calculate with uint*/
inline Cigint operator+(const Cigint &lhs, uint rhs) {
	return cigint_add(lhs, rhs);
}

inline const Cigint &operator+=(Cigint &lhs, uint rhs) {
	lhs = cigint_add(lhs, rhs);
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

inline bool operator>=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) >= 0;
}

inline bool operator<=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) <= 0;
}
#endif
