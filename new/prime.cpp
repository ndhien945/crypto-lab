#define BI_BIT 512
#include <chrono>
#include <iomanip>
#include <iostream>
#include <sstream>

#include "bigint.h"

constexpr u32 POLY_R = 14;
struct Poly : std::array<bui, POLY_R>{};

Poly poly_pow_1x(const bui &n) {
	Poly base{};
	base[0] = bui1(); base[1] = bui1();
	Poly res{};
	res[0] = bui1();
	return res;
}

int main() {
	bui u = bui_from_dec("260428835329122752520818469321216072583938198616075453742527759001901820374664228839496959095353854544158481165265966459");
	// bui u = bui_from_dec("260428835329122752520818469321216072583938198616075453742527");
	bui v = bui_from_dec("1312312317639123213");
	// bui m = bui_from_dec("108579795932485217312615519053");
	bui m = bui_from_dec("823887783191267813656599693818502133610549771176609410328824491902309472167445766968176579098197424208002485918297593219");

	// bui u = bui_from_dec("123456789");
	// bui v = bui_from_dec("6713");
	// bui m = bui_from_dec("896947");

	// auto sm = shift_mod(u, 400, m);
	// printf("sm = %s\n", bui_to_dec(sm).c_str());
	// return 0;

	printf("u = %s\n", bui_to_dec(u).c_str());
	printf("u = %s\n", bui_to_hex(u).c_str());
	printf("v = %s\n", bui_to_dec(v).c_str());
	printf("v = %s\n", bui_to_hex(v).c_str());
	printf("m = %s\n", bui_to_dec(m).c_str());


	auto start_mont = std::chrono::high_resolution_clock::now();
	MontgomeryReducer mr(m);
	// printf("reducerBits= %d\n", mr.reducerBits);
	// printf("reciprocal = %s\n", bui_to_dec(mr.reciprocal).c_str());
	// printf("mask       = %s\n", bui_to_dec(mr.mask).c_str());
	// printf("reducer    = %s\n", bui_to_dec(mr.reducer).c_str());
	// printf("factor     = %s\n", bui_to_dec(mr.factor).c_str());
	// printf("c1         = %s\n", bui_to_dec(mr.convertedOne).c_str());

	auto cu = mr.convertIn(u);
	// auto ou = mr.convertOut(cu);
	// printf("cu= %s\n", bui_to_dec(cu).c_str());
	// printf("ou= %s\n", bui_to_dec(ou).c_str());
	// printf("o1= %s\n", bui_to_dec(mr.convertedOne).c_str());
	// ---------- Time Montgomery exponentiation ----------
	auto c = mr.pow(cu, v);
	auto cc = mr.convertOut(c);
	auto end_mont = std::chrono::high_resolution_clock::now();
	auto duration_mont = std::chrono::duration_cast<std::chrono::nanoseconds>(end_mont - start_mont).count();

	printf("Montgomery pow: c    = %s\n", bui_to_dec(c).c_str());
	printf("Converted out: cc    = %s\n", bui_to_dec(cc).c_str());

	// ---------- Time standard modular exponentiation ----------
	auto start_std = std::chrono::high_resolution_clock::now();
	auto c1 = pow_mod(u, v, m);
	auto end_std = std::chrono::high_resolution_clock::now();
	auto duration_std = std::chrono::duration_cast<std::chrono::nanoseconds>(end_std - start_std).count();

	printf("Standard pow_mod: c1 = %s\n", bui_to_dec(c1).c_str());
	printf("--------------------------------\n");
	printf("Montgomery pow time  : %lld ns\n", duration_mont);
	printf("Standard pow_mod time: %lld ns\n", duration_std);

	return 0;
}
