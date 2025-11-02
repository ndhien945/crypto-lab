#include <chrono>
#include <iostream>
#include <string>
#define CIGINT_IMPLEMENTATION
#define CIGINT_STRIP_PREFIX
#define CIGINT_N (512 / 32)
#include <iomanip>

#include "cigint.h"

using namespace std::chrono;

void cigint_fill_random(Cigint* cig) {
	for (size_t i = 0; i < CIGINT_N; i++) {
		u32 r = (u32)rand();
		r = (r << 16) ^ (u32)rand();
		cig->data[i] = r;
	}
}

#include "benchmark.h"
// observable sink to block DCE
static volatile u32 g_sink = 0;
inline void consume(const Cigint& x) {
	u32 acc = 0;
	for (size_t i = 0; i < CIGINT_N; ++i) acc ^= x.data[i]; g_sink ^= acc;
}

// ------------------------------------------------------------
// 1) by-value functions: Cigint f(Cigint, Cigint)
// ------------------------------------------------------------
template<typename F>
void bench_func(const std::string& name, F f, const Cigint& a, const Cigint& b) {
    volatile F fp = f; // block inlining
	bench(name, [&]{
        Cigint r = (*fp)(a, b);
		consume(r);
	});
}

// ------------------------------------------------------------
// 2) in-place, RHS is effectively const: void f(Cigint*, const Cigint*)
//    (your old bench_func_ref)
// ------------------------------------------------------------
template<typename F>
void bench_func_ref(const std::string& name, F f, const Cigint& a, const Cigint& b) {
    volatile F fp = f;
	bench(name, [&]{
        Cigint x = a;
		Cigint y = b;
        (*fp)(&x, &y);
		consume(x);
	});
}

// ------------------------------------------------------------
// 4) 3-arg: void f(const Cigint*, const Cigint*, Cigint*)
//    (your bench_func_refex)
// ------------------------------------------------------------
template<typename F>
void bench_func_refex(const std::string& name, F f, const Cigint& a, const Cigint& b, const Cigint& r0) {
	volatile F fp = f;
	bench(name, [&]{
		Cigint lhs = a;
		Cigint rhs = b;
		Cigint res = r0;
		(*fp)(&lhs, &rhs, &res);
		consume(res);
	});
}

Cigint cigint_add_fast_1(Cigint a, Cigint b) {
	Cigint r = CIGINT_ZERO();
	uint64_t carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		uint64_t sum = (uint64_t)a.data[i] + (uint64_t)b.data[i] + carry;
		r.data[i] = (u32)sum;
		carry = sum >> 32;
	}
	return r;
}

Cigint cigint_add_fast_2(Cigint a, Cigint b) {
	Cigint r = CIGINT_ZERO();
	u32 carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		u32 sum = a.data[i] + b.data[i] + carry;
		r.data[i] = sum;
		carry = sum < a.data[i] || sum < b.data[i];
	}
	return r;
}

// In-place (Reference) Functions
void cigint_add_fast_1_r(Cigint *a, Cigint *b) {
	uint64_t carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		uint64_t sum = (uint64_t)a->data[i] + (uint64_t)b->data[i] + carry;
		a->data[i] = (u32)sum;
		carry = sum >> SIZEOF_U32;
	}
}

void cigint_add_fast_1_a(Cigint *a, Cigint *b) {
	uint64_t sum = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		sum = (uint64_t)a->data[i] + (uint64_t)b->data[i] + (sum >> SIZEOF_U32);
		a->data[i] = (u32)sum;
	}
}

void cigint_add_fast_1_b(Cigint *a, Cigint *b) {
	for (size_t i = CIGINT_N; i-- > 0;) {
		a->data[i] = (u32) (uint64_t)a->data[i] + (uint64_t)b->data[i] + ((uint64_t) a->data[i + 1] >> 32);
	}
}

void cigint_add_fast_2_r(Cigint *a, Cigint *b) {
	u32 carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		u32 sum = a->data[i] + b->data[i] + carry;
		carry = sum < a->data[i] || sum < b->data[i];
		a->data[i] = sum;
	}
}

void cigint_add_fast_2_a(Cigint *a, Cigint *b) {
	u32 sum = -1;
	for (size_t i = CIGINT_N; i-- > 0;) {
		sum = a->data[i] + b->data[i] + (sum < a->data[i] || sum < b->data[i]);
		a->data[i] = sum;
	}
}

void cigint_add_fast_2_a_i(Cigint *a, Cigint *b) {
	u32 sum = -1;
	u32 carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		sum = a->data[i] + b->data[i] + carry;
		carry = sum < a->data[i] | sum < b->data[i];
		a->data[i] = sum;
	}
}

void cigint_add_fast_2_b(Cigint *a, Cigint *b) {
	u32 carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		a->data[i] += b->data[i] + carry;
		carry = a->data[i] < b->data[i] || (carry && a->data[i] < carry);
	}
}

void cigint_add_fast_2_d(Cigint *a, Cigint *b) {
	u32 carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		u32 sum = a->data[i] + b->data[i] + carry;
		carry = sum < a->data[i] || sum < b->data[i];
		a->data[i] = sum;
	}
}

void cigint_add_fast_2_b_i(Cigint* a, Cigint* b) {
	u32 carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		u32 x = a->data[i];
		u32 y = b->data[i];

		u32 s  = x + y;          // first add
		u32 c1 = (s < x);        // overflow from x+y?
		u32 t  = s + carry;      // add incoming carry
		u32 c2 = (t < s);        // overflow from +carry?

		a->data[i] = t;
		carry = c1 | c2;              // next carry
	}
}

void cigint_add_fast_2_b_iii(Cigint* a, Cigint* b) {
	u32 carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		u32 x = a->data[i];
		u32 y = b->data[i];
		u32 s  = x + y;
		u32 t  = s + carry;
		a->data[i] = t;
		carry = s < x | t < s;
	}
}

void cigint_add_fast_2_b_iv(Cigint* a, Cigint* b) {
	u32 carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		u32 s  = a->data[i] + b->data[i];
		u32 t  = s + carry;
		carry = s < a->data[i] | t < s;
		a->data[i] = t;
	}
}

void cigint_add_fast_2_b_ii(Cigint* a, Cigint* b) {
	u32 carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		u32 x = a->data[i], y = b->data[i];
		u32 t = x + y + carry;       // full sum
		a->data[i] = t;
		// carry-out of x + y + carry (2's complement identity)
		carry = (x & y | ((x | y) & ~t)) >> 31;
	}
}

void cigint_add_fast_2_b_ptr(Cigint* a, Cigint* b) {
	u32 carry = 0;
	u32*       pa = a->data + CIGINT_N;
	const u32* pb = b->data + CIGINT_N;
	do {
		--pa; --pb;
		u32 x = *pa, y = *pb;
		u32 s = x + y;          u32 c1 = (s < x);
		u32 t = s + carry;      u32 c2 = (t < s);
		*pa = t;
		carry = c1 | c2;
	} while (pa != a->data);
}

void cigint_add_fast_2_b_ptr2(Cigint* a, Cigint* b) {
	u32 carry = 0;
	u32*       pa = a->data + CIGINT_N;
	const u32* pb = b->data + CIGINT_N;
	do {
		--pa; --pb;
		u32 x = *pa, y = *pb;
		u32 s = x + y;
		u32 t = s + carry;
		*pa = t;
		carry = s < x | t < s;
	} while (pa != a->data);
}

void cigint_add_fast_2_c(Cigint *a, Cigint *b) {
    u32 carry = 0;
    for (size_t i = CIGINT_N; i-- > 0;) {
        u32 prev = a->data[i];
        a->data[i] += b->data[i] + carry;
        carry = a->data[i] < prev || (carry && a->data[i] == prev);
    }
}

// void cigint_add_fast_2_c(Cigint *a, Cigint *b) {
// 	for (size_t i = CIGINT_N; i-- > 0;) {
// 		a->data[i] = (a->data[i] += b->data[i]) + (a->data[i] < b->data[i]);
// 	}
// }

Cigint cigint_add_fast_2_d_c(Cigint a, Cigint b) {
	cigint_add_fast_2_d(&a, &b);
	return a;
}

Cigint cigint_add_fast_2_d_o(Cigint a, Cigint b) {
	u32 carry = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		u32 sum = a.data[i] + b.data[i] + carry;
		carry = sum < a.data[i] || sum < b.data[i];
		a.data[i] = sum;
	}
	return a;
}

// #include <immintrin.h>
// static inline void cigint_add_adc_ip(Cigint* a, const Cigint* b) {
// 	unsigned char c = 0;
// 	for (size_t i = CIGINT_N; i-- > 0;) {
// 		c = _addcarry_u32(c, a->data[i], b->data[i], &a->data[i]);
// 	}
// }
//
// static inline Cigint cigint_add_adc(Cigint x, const Cigint& y) {
// 	cigint_add_adc_ip(&x, &y);
// 	return x;
// }

void cigint_add_ref_old(Cigint *lhs, Cigint *rhs) {
	while (!cigint_is0_ref(rhs)) {
		Cigint carry = cigint_and(*lhs, *rhs);
		cigint_xor_ref(lhs, rhs);
		*rhs = cigint_shl(carry, 1);
	}
}

Cigint cigint_add_old(Cigint lhs, Cigint rhs) {
	while (!cigint_is0(rhs)) {
		Cigint carry = cigint_and(lhs, rhs);
		lhs = cigint_xor(lhs, rhs);
		rhs = cigint_shl(carry, 1);
	}
	return lhs;
}

void benchmark() {
	Cigint a, b;
	cigint_fill_random(&a);
	cigint_fill_random(&b);
	Cigint r = a;

	// a = 1;
	// b = 2;
	// r = cigint_mul(a, b);
	// cprintf("mul = %Cd\n", r);
	// r = a;
	// cigint_mul_ref(&r, &b);
	// cprintf("mul_ref = %Cd\n", r);
	// r = a;
	// a = 0;
	// b = 0xFFFFFFFF;
	// r = cigint_mul(a, b);
	// cprintf("mul = %Cd\n", r);
	// r = a;
	// cigint_mul_ref(&r, &b);
	// cprintf("mul_ref = %Cd\n", r);

	cigint_fill_random(&a);
	cigint_fill_random(&b);
	cigint_printf("a = %Cd\n", a);
	std::cout << "a = " << a << "\n";
	std::cout << "b = " << b << "\n";
	bench_func_ref("add_ref", cigint_add_ref, a, b);
	bench_func_ref("add_ref", cigint_add_ref, a, b);
	bench_func_ref("add_ref_old", cigint_add_ref_old, a, b);
	bench_func("add_old", cigint_add_old, a, b);
	bench_func("add", cigint_add, a, b);
	bench_func_ref("mul_ref", cigint_mul_ref, a, b);
	bench_func_refex("mul_refex", cigint_mul_refex, a, b, r);
	bench_func_ref("mul_ref2", cigint_mul_ref2, a, b);
	bench_func_ref("mul_ref3", cigint_mul_ref3, a, b);
	bench_func_ref("mul_ref_old", cigint_mul_ref_old, a, b);
	bench_func("mul_old", cigint_mul_old, a, b);
	std::cout << "a = " << a << "\n";
	std::cout << "b = " << b << "\n";
}

int main() {
	srand((unsigned int)time(NULL));  // Initialize random number generator
	benchmark();
	return 0;
}

// a = 759480307011953463468328532656259629625734757261525159780721102534358014148939345155444885268762564303576054958843407900809783642799109643494134892615670
// b = 1851399520923607203120963818347025007257247084972234839639630771977617926347525576181116318869116385755354715237252143688539590208070507383212645245605940
// add_ref                   | first:        300 ns | total_loop:      1166800 ns | mean_loop:      11.67 ns | total_body:      3062500 ns | mean_body:      30.62 ns
// add_ref                   | first:        200 ns | total_loop:      1200800 ns | mean_loop:      12.01 ns | total_body:      4206500 ns | mean_body:      42.06 ns
// add_ref_old               | first:      16600 ns | total_loop:     15198000 ns | mean_loop:     151.98 ns | total_body:     18317500 ns | mean_body:     183.18 ns
// add_old                   | first:        400 ns | total_loop:     15977800 ns | mean_loop:     159.78 ns | total_body:     17229700 ns | mean_body:     172.30 ns
// add                       | first:        200 ns | total_loop:      1117700 ns | mean_loop:      11.18 ns | total_body:      3691300 ns | mean_body:      36.91 ns
// mul_ref                   | first:        600 ns | total_loop:      5419900 ns | mean_loop:      54.20 ns | total_body:      8105700 ns | mean_body:      81.06 ns
// mul_refex                 | first:        300 ns | total_loop:      5233700 ns | mean_loop:      52.34 ns | total_body:     10210500 ns | mean_body:     102.11 ns
// mul_ref2                  | first:        600 ns | total_loop:     18298400 ns | mean_loop:     182.98 ns | total_body:     19707300 ns | mean_body:     197.07 ns
// mul_ref3                  | first:        500 ns | total_loop:      5980800 ns | mean_loop:      59.81 ns | total_body:      8533400 ns | mean_body:      85.33 ns
// mul_ref_old               | first:      14900 ns | total_loop:   1128302400 ns | mean_loop:   11283.02 ns | total_body:   1105397200 ns | mean_body:   11053.97 ns
// mul_old                   | first:       9800 ns | total_loop:    919708900 ns | mean_loop:    9197.09 ns | total_body:    932545400 ns | mean_body:    9325.45 ns