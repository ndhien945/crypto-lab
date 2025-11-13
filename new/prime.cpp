#define BI_BIT 512
#include <iostream>

#include "bigint.h"

constexpr u32 POLY_R = 14;
struct Poly : std::array<bui, POLY_R>{};

inline bui mod_nat(bui x, const bui &b) {
	while (cmp(x, b) >= 0) sub_ip(x, b);
	return x;
}

Poly poly_pow_1x(const bui &n) {
	Poly base{};
	base[0] = bui1(); base[1] = bui1();
	Poly res{};
	res[0] = bui1();
	return res;
}

inline void divmod(const bui &a, const bui &b, bui *q, bui *r) {
	assert(!bui_is0(b) && "Division by zero");

	int cmpres = cmp(a, b);
	if (cmpres < 0) {
		if (q) *q = {};
		if (r) *r = a;
		return;
	}
	if (cmpres == 0) {
		if (q) *q = bui1();
		if (r) *r = {};
		return;
	}

	bui quotient{};
	bui remainder = a;

	// Determine bit difference between dividend and divisor
	u32 shift = highest_bit(a) - highest_bit(b);

	// Extend divisor into bul for safe shifting
	bul denom = bui_to_bul(b);
	shift_left_ip(denom, shift);

	for (int i = shift + 1; i-- > 0;) {
		// Compare high BI_N bits of denom with remainder
		bui denom_high = bul_low(denom); // low part holds the aligned bits
		if (cmp(remainder, denom_high) >= 0) {
			sub_ip(remainder, denom_high);
			quotient = set_bit(quotient, i, 1);
		}
		shift_right_ip(denom, 1);
	}

	if (q) *q = quotient;
	if (r) *r = remainder;
}

int main() {
	bui a = bui_from_dec("115792089237316195423570985008687907853269984665640564039457584007913129639");
	bui b = bui_from_dec("123456789123456789");
	// bui b = bui_from_dec("2");
	printf("A = %s\n", bui_to_dec(a).c_str());
	printf("B = %s\n", bui_to_dec(b).c_str());
	bui r;
	bui q;
	divmod_knuth(a, b, q, r);
	auto t0 = mul(b, q);
	auto r3 = bui_to_bul(a);
	sub_ip(r3, t0);
	printf("Q = %s\n", bui_to_dec(q).c_str());
	printf("R = %s\n", bui_to_dec(r).c_str());
	printf("R3= %s\n", bui_to_dec(bul_low(r3)).c_str());
	bui r2;
	divmod(a, b, NULL, &r2);
	printf("R2= %s\n", bui_to_dec(r2).c_str());
}
