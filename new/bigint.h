#ifndef _BIGINT_H_
#define _BIGINT_H_
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <string>

typedef uint32_t u32;
typedef uint64_t u64;

#ifndef BI_N
#define BI_N (512 / 32)
#endif

#if defined(__GNUC__) || defined(__clang__)
#define GNU_BUILTIN
#endif

#if defined(_MSC_VER)
#define ALWAYS_INLINE __forceinline
#elif defined(__GNUC__) || defined(__clang__)
#define ALWAYS_INLINE inline __attribute__((always_inline))
#else
#define ALWAYS_INLINE inline
#endif

// big endian: data[0] = MSW
struct bui : std::array<u32, BI_N> {};
struct bul : std::array<u32, BI_N * 2> {};

constexpr bui bui0() { return {}; }

constexpr bui bui1() {
	bui r = {}; r[BI_N - 1] = 1;
	return r;
}

constexpr bui bui_from_u32(const u32 x) {
	bui r = {}; r[BI_N - 1] = x;
	return r;
}

constexpr bul bul0() { return {}; }

constexpr bul bul1() {
	bul r = {}; r[BI_N * 2 - 1] = 1;
	return r;
}

inline bul bul_from_u32(const u32 x) {
	bul r = {}; r[BI_N * 2 - 1] = x;
	return r;
}

inline bool bui_is0(const bui& x) {
	for (const u32 val : x)
		if (val != 0) return false;
	return true;
}

inline bui bul_low(bul& x) {
	bui r{};
	std::copy(x.begin() + BI_N, x.end(), r.begin());
	return r;
}

inline bui bul_high(const bul& x) {
	bui r{};
	std::copy_n(r.begin(), BI_N, r.begin());
	return r;
}

inline bul bui_to_bul(const bui& input) {
	bul r{};
	std::copy(input.begin(), input.end(), r.begin() + BI_N);
	return r;
}

std::string bui_to_dec(const bui& x);
bui bui_from_dec(const std::string& s);

int cmp(const bui &a, const bui &b);
void add_ip(bui& a, const bui& b);
void add_ip(bul& a, const bul& b);
void sub_ip(bui& a, const bui& b);

inline int cmp(const bui &a, const bui &b) {
	for (u32 i = 0; i < BI_N; ++i) {
		if (a[i] != b[i])
			return a[i] > b[i] ? 1 : -1;
	}
	return 0;
}

// a += b;
inline void add_ip(bui& a, const bui& b) {
	u32 c = 0, i = BI_N;
	while (i-- > 0) {
#ifdef GNU_BUILTIN
		c = __builtin_add_overflow(a[i], b[i] + c, &a[i]);
#else
		u64 s = (u64)a[i] + b[i] + c;
		a[i] = (u32)s;
		c = s >> 32;
#endif
	}
}

// a += b
inline void add_ip(bul& a, const bul& b) {
	u32 c = 0, i = BI_N * 2;
	while (i-- > 0) {
#ifdef GNU_BUILTIN
		c = __builtin_add_overflow(a[i], b[i] + c, &a[i]);
#else
		u64 s = (u64)a[i] + b[i] + c;
		a[i] = (u32)s;
		c = s >> 32;
#endif
	}
}

inline void add_ip_n(u32* a, const u32* b, const u32 size) {
	u32 c = 0, i = size;
	while (i-- > 0) {
#ifdef GNU_BUILTIN
		c = __builtin_add_overflow(a[i], b[i] + c, &a[i]);
#else
		u64 s = (u64)a[i] + b[i] + c;
		a[i] = (u32)s;
		c = s >> 32;
#endif
	}
}

inline void add_n(const u32* a, const u32* b, u32* r, const u32 size) {
	u32 c = 0, i = size;
	while (i-- > 0) {
#ifdef GNU_BUILTIN
		c = __builtin_add_overflow(a[i], b[i] + c, &r[i]);
#else
		u64 s = (u64)a[i] + b[i] + c;
		r[i] = (u32)s;
		c = s >> 32;
#endif
	}
}

// r = a + b
inline bui add(bui a, const bui& b) {
	add_ip(a, b);
	return a;
}

// a = (a + b) % m
inline void add_mod_ip(bui &a, const bui &b, const bui &m) {
	u32 c = 0;
	for (u32 i = BI_N; i-- > 0;) {
#ifdef GNU_BUILTIN
		c = __builtin_add_overflow(a[i], b[i] + c, &a[i]);
#else
		u64 s = (u64)a[i] + (u64)b[i] + c;
		a[i] = (u32)s;
		c = s >> 32;
#endif
	}
	if (c || cmp(a, m) >= 0) {
		sub_ip(a, m);
	}
}

// a -= b; // assume a > b
inline void sub_ip(bui& a, const bui& b) {
	u32 borrow = 0, i = BI_N;
	while (i-- > 0) {
#ifdef GNU_BUILTIN
		borrow = __builtin_sub_overflow(a[i], b[i] + borrow, &a[i]);
#else
		u64 d = (u64)a[i] - b[i] - borrow;
		a[i] = static_cast<u32>(d);
		borrow = d > a[i] ? 1 : 0; // borrow occurs if there is underflow
#endif
	}
}

inline void sub_ip(bul& a, const bul& b) {
	u32 borrow = 0, i = BI_N * 2;
	while (i-- > 0) {
#ifdef GNU_BUILTIN
		borrow = __builtin_sub_overflow(a[i], b[i] + borrow, &a[i]);
#else
		u64 d = (u64)a[i] - b[i] - borrow;
		a[i] = static_cast<u32>(d);
		borrow = d > a[i] ? 1 : 0; // borrow occurs if there is underflow
#endif
	}
}

// a -= b; // assume a > b
inline void sub_n(const u32* a, const u32* b, u32* r, u32 size) {
	u32 borrow = 0;
	while (size-- > 0) {
#ifdef GNU_BUILTIN
		borrow = __builtin_sub_overflow(a[size], b[size] + borrow, &r[size]);
#else
		u64 d = (u64)a[size] - b[size] - borrow;
		r[size] = (u32)d;
		borrow = d > a[size] ? 1 : 0; // borrow occurs if there is underflow
#endif
	}
}

inline bui sub(bui a, const bui& b) {
	sub_ip(a, b);
	return a;
}

inline void mul_ref(const bui &a, const bui &b, bul &r) {
	for (u32 i = BI_N; i-- > 0;) {
		u32 c = 0;
		for (u32 j = BI_N; j-- > 0;) {
			u64 p = (u64)a[i] * b[j] + r[i + j + 1] + c;
			r[i + j + 1] = (u32)p;
			c = p >> 32;
		}
		r[i] += c;
	}
}

inline void mul_ip(bui &a, const bui &b) {
	bul r{};
	mul_ref(a, b, r);
	a = bul_low(r);
}

inline bul mul(const bui& a, const bui& b) {
	bul r{};
	mul_ref(a, b, r);
	return r;
}

inline bui mul_low(const bui& a, const bui& b) {
	bul r = mul(a, b);
	return bul_low(r);
}

inline void bui_u32divmod(const bui& a, u32 b, bui& q, u32& r) {
	q = {};
	r = 0;
	for (int i = 0; i < BI_N; ++i) {
		u64 dividend = (u64)r << 32 | a[i];
		q[i] = (u32)(dividend / b);
		r = (u32)(dividend % b);
	}
}

inline bool is_space_c(char c) {
	return c == ' ' || c == '\t';
}

ALWAYS_INLINE u32 dbl_ip_imp(bui &x) {
	u32 c = 0, i = BI_N;
	while (i-- > 0) {
		u32 v = x[i];
		u32 nv = v << 1 | c;
		c = v >> 31;
		x[i] = nv;
	}
	return c;
}

// x = 2x (= x << 1)
inline void dbl_ip(bui &x) {
	dbl_ip_imp(x);
}

// x = (2x) % m
static void dbl_mod_ip(bui &x, const bui &m) {
	if (dbl_ip_imp(x) || cmp(x, m) >= 0)
		sub_ip(x, m);
}

inline int hex_val(unsigned char c) {
	if (c >= '0' && c <= '9') return c - '0';
	if (c >= 'a' && c <= 'f') return 10 + (c - 'a');
	if (c >= 'A' && c <= 'F') return 10 + (c - 'A');
	return -1;
}

std::string bui_to_dec(const bui& x) {
	std::string result;
	if (bui_is0(x)) return "0";
	u32 rems[(BI_N * 32 + 26) / 27];
	size_t count = 0;
	bui n = x;
	bui q;
	while (!bui_is0(n)) {
		u32 r;
		bui_u32divmod(n, 100000000U, q, r);
		rems[count++] = r;
		n = q;
	}
	// first chunk is printed without leading zeros
	result += std::to_string(rems[count - 1]);
	// remaining chunks, padded with leading zeros
	for (size_t i = count - 2; i < count; --i) {
		result += std::string(8 - std::to_string(rems[i]).size(), '0') + std::to_string(rems[i]);
	}
	return result;
}

bui bui_from_dec(const std::string& s) {
	assert(!s.empty() && "bui_from_dec: empty string");
	size_t i = 0;
	// skip leading spaces and optional '+'
	while (is_space_c(s[i])) ++i;
	if (s[i] == '+') ++i;
	assert(s[i] != '-' && "bui_from_dec: negative not supported");
	// skip leading zeros, underscores, spaces
	while (s[i] == '0' || s[i] == '_') ++i;
	bool any_digit = false;
	// process each digit in the decimal string
	constexpr bui n10 = bui_from_u32(10u);
	bui out{};
	bui tmp{};
	for (; i < s.size(); ++i) {
		char c = s[i];
		if (c == '_' || is_space_c(c)) continue;
		if (c < '0' || c > '9') break;
		any_digit = true;
		mul_ip(out, n10);
		tmp[BI_N - 1] = c - '0';
		add_ip(out, tmp);
	}
	assert(any_digit && "bui_from_dec: no digits found");
	return out;
}

inline u32 highest_limb(const bui &x) {
	for (size_t i = 0; i < BI_N; ++i)
		if (x[i] > 0) return BI_N - i - 1;
	return 0;
}

inline void shift_limb_left(bul &x, u32 l) {
	if (l == 0) return;
	if (l >= BI_N * 2) {
		std::fill(x.begin(), x.end(), 0);
		return;
	}
	std::copy(x.begin() + l, x.end(), x.begin());
	std::fill(x.end() - l, x.end(), 0);
}

ALWAYS_INLINE void split_bui(const bui &x, bui &high, bui &low, u32 size) {
	std::copy_n(x.begin(), size, high.begin() + (BI_N - size));
	std::copy(x.begin() + size, x.end(), low.begin() + size);
}

inline bul karatsuba(const bui &a, const bui &b, u32 size) {
	bul r{};
	if (size <= 16) return mul(a, b);
	u32 half = size / 2;

	bui a1{}, a0{}, b1{}, b0{};
	split_bui(a, a1, a0, half);
	split_bui(b, b1, b0, half);

	bul z0 = karatsuba(a0, b0, half);
	bul z2 = karatsuba(a1, b1, half);

	bui a_sum = add(a1, a0);
	bui b_sum = add(b1, b0);
	bul z1 = karatsuba(a_sum, b_sum, half);
	sub_ip(z1, z2);
	sub_ip(z1, z0);

	shift_limb_left(z2, 2 * half);
	shift_limb_left(z1, half);

	add_ip(r, z0);
	add_ip(r, z1);
	add_ip(r, z2);
	return r;
}

#include <vector>
inline void mul_ip_n(const u32* a, const u32* b, u32* r, size_t n) {
    std::fill_n(r, 2 * n, 0);
	for (u32 i = n; i-- > 0;) {
		u32 c = 0;
		for (u32 j = n; j-- > 0;) {
			u64 p = (u64)a[i] * b[j] + r[i + j + 1] + c;
			r[i + j + 1] = (u32)p;
			c = p >> 32;
		}
		r[i] += c;
	}
}

constexpr size_t KARATSUBA_CUTOFF = 2;
// constexpr size_t KARATSUBA_CUTOFF = 32; // tune this experimentally
inline void karatsuba_be_rec(const u32* a, const u32* b, u32* r, u32 n, u32* scratch) {
    if (n <= KARATSUBA_CUTOFF) {
        mul_ip_n(a, b, r, n);
        return;
    }

    u32 half = n / 2;
    const u32* a1 = a;
    const u32* a0 = a + half;
    const u32* b1 = b;
    const u32* b0 = b + half;

    u32* z2 = r;       // high part
    u32* z0 = r + n;   // low part
    u32* z1 = scratch; // middle temp (2*half)

    u32* tmp_a = z1 + 2 * half;
    u32* tmp_b = tmp_a + half;
    u32* tmp_scratch = tmp_b + half;

    karatsuba_be_rec(a0, b0, z0, half, tmp_scratch); // z0 = a0 * b0
    karatsuba_be_rec(a1, b1, z2, half, tmp_scratch); // z2 = a1 * b1

	add_n(a1, a0, tmp_a, half); // tmp_a = a1 + a0
	add_n(b1, b0, tmp_b, half); // tmp_b = b1 + b0
    karatsuba_be_rec(tmp_a, tmp_b, z1, half, tmp_scratch); // z1 = (a1 + a0) * (b1 + b0)

    // z1 = z1 - z2 - z0
	sub_n(z1, z2, z1, 2 * half);
	sub_n(z1, z0, z1, 2 * half);
    // combine: r = z2 << (2*half*32) + z1 << (half*32) + z0
	add_n(r + half, z1, r + half, 2 * half);
}

inline bul karatsuba_be_top(const bui& a, const bui& b) {
    constexpr size_t n = BI_N;
	// u32 n = std::max(highest_limb(a), highest_limb(b));
    bul r{};
    std::vector<u32> scratch(6 * n, 0);
    karatsuba_be_rec(a.data(), b.data(), r.data(), n, scratch.data());
    return r;
}

// for compatibility with your test code
inline bul karatsu_test(const bui& a, const bui& b) {
    return karatsuba_be_top(a, b);
}


#endif