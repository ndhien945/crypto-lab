#include <iostream>
#include <ostream>

#include "../bigint.h"
// Returns 0 on success, 1 on invalid parameters (v == 0, n < 2, m < n, …)

constexpr u32 B    = 0x1'0000'000u;          // 2^32, the base of one limb
constexpr u64 BB   = 0x1'0000'0000ull;

typedef int64_t i64;

int countl_zero(uint64_t x) {
    if (x == 0) return 64;
    return __builtin_clzll(x);
}

// Helper: get limb at logical position k (0 = LSB of number)
inline u32 get(const bui& a, int k, int len) {
    int idx = BI_N - len + k;
    return (k < len) ? a[idx] : 0;
}

// Helper: set limb
inline void set(bui& a, int k, int len, u32 val) {
    int idx = BI_N - len + k;
    if (k < len) a[idx] = val;
}

int divmnu_bui(
    bui* q_out,
    bui* r_out,
    const bui& u,
    const bui& v,
    int m,
    int n)
{
    if (m < n || n < 2 || get(v, n-1, n) == 0) return 1;

    // --- D1: Normalize ---
    u32 v_msb = get(v, n-1, n);
    int s = countl_zero(v_msb);
    if (s == 32) return 1;

    std::array<u32, BI_N + 1> un{};
    std::array<u32, BI_N>     vn{};

    // Normalize v
    for (int i = n-1; i >= 0; --i) {
        u32 hi = get(v, i, n);
        u32 lo = (i > 0) ? get(v, i-1, n) : 0;
        vn[BI_N - n + i] = (hi << s) | (lo >> (32 - s));
    }

    // Normalize u
    un[BI_N] = get(u, m-1, m) >> (32 - s);
    for (int i = m-1; i >= 0; --i) {
        u32 hi = get(u, i, m);
        u32 lo = (i > 0) ? get(u, i-1, m) : 0;
        un[BI_N - m + i] = (hi << s) | (lo >> (32 - s));
    }

    // --- Main loop ---
    for (int j = m - n; j >= 0; --j) {
        int un_jn  = BI_N - (m - n - j);
        int un_jn1 = un_jn - 1;
        int un_jn2 = un_jn - 2;

        u64 top = (u64(un[un_jn]) * B) + un[un_jn1];
        u64 qhat = top / vn[BI_N - 1];
        u64 rhat = top % vn[BI_N - 1];

        while (qhat >= B ||
               qhat * u64(vn[BI_N - 2]) > B * rhat + un[un_jn2]) {
            --qhat;
            rhat += vn[BI_N - 1];
            if (rhat >= B) break;
        }

        // Multiply and subtract
        i64 borrow = 0;
        for (int i = 0; i < n; ++i) {
            int v_idx = BI_N - 1 - i;
            int u_idx = un_jn - i;
            u64 p = qhat * u64(vn[v_idx]);
            i64 t = i64(un[u_idx]) - borrow - (p & 0xFFFFFFFFULL);
            un[u_idx] = u32(t);
            borrow = (p >> 32) - (t >> 32);
        }
        i64 t = i64(un[un_jn]) - borrow;
        un[un_jn] = u32(t);

        u32 qdigit = u32(qhat);
        if (t < 0) {
            --qdigit;
            u64 carry = 0;
            for (int i = 0; i < n; ++i) {
                int v_idx = BI_N - 1 - i;
                int u_idx = un_jn - i;
                u64 sum = u64(un[u_idx]) + vn[v_idx] + carry;
                un[u_idx] = u32(sum);
                carry = sum >> 32;
            }
            un[un_jn] += u32(carry);
        }

        if (q_out) set(*q_out, j, m-n+1, qdigit);
    }

    // --- Unnormalize remainder ---
    if (r_out) {
        for (int i = 0; i < n; ++i) {
            int src_idx = BI_N - n + i;
            u32 hi = un[src_idx] >> s;
            u32 lo = (i < n-1) ? (un[src_idx + 1] << (32 - s)) : 0;
            set(*r_out, i, n, hi | lo);
        }
    }

    return 0;
}

constexpr int LIMBS = 8;
bui u{}, v{}, q{}, rem{};

int main() {
    // 2^256 - 1  divided by  0x12345678'9ABCDEF0'11223344'55667788
    u.fill(0xFFFF'FFFFu);
    v[BI_N - 4] = 0x55667788u;
    v[BI_N - 3] = 0x11223344u;
    v[BI_N - 2] = 0x9ABCDEF0u;
    v[BI_N - 1] = 0x12345678u;

    int m = 8;          // dividend length
    int n = 4;              // divisor length

    int rc = divmnu_bui(&q, &rem, u, v, m, n);
    if (rc) {
        std::cout << "Error\n";
    }
    printf("A: %s\n", bui_to_dec(u).c_str());
    printf("B: %s\n", bui_to_dec(v).c_str());
    printf("Q: %s\n", bui_to_dec(q).c_str());
    printf("R: %s\n", bui_to_dec(rem).c_str());
}