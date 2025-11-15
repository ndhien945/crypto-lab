#include <iostream>
#include <chrono>
#include <vector>
#include <random>
#include <cstdint>

typedef uint32_t u32;
typedef uint64_t u64;

constexpr size_t N = 1024;

inline void add_n_builtin(const u32* a, const u32* b, u32* r, const u32 size) {
    u32 c = 0, t;
    for (u32 i = size; i-- > 0;) {
        bool carry1 = __builtin_add_overflow(b[i], c, &t);
        bool carry2 = __builtin_add_overflow(a[i], t, &r[i]);
        c = carry1 || carry2;
    }
}

inline void add_n_builtin_ov(const u32* a, const u32* b, u32* r, const u32 size) {
    u32 c = 0;
    for (u32 i = size; i-- > 0;) {
        c = __builtin_add_overflow(b[i], a[i] + c, &r[i]);
    }
}

inline void add_n_64bit(const u32* a, const u32* b, u32* r, const u32 size) {
    u32 c = 0;
    for (u32 i = size; i-- > 0;) {
        u64 s = (u64)a[i] + b[i] + c;
        r[i] = (u32)s;
        c = s >> 32;
    }
}

int main() {
    std::vector<u32> a(N), b(N), r(N);

    std::mt19937 rng(42);
    std::uniform_int_distribution<u32> dist(0, 0xFFFFFFFF);

    for (size_t i = 0; i < N; ++i) {
        a[i] = dist(rng);
        b[i] = dist(rng);
    }

    // Benchmark GNU builtin
    auto start = std::chrono::high_resolution_clock::now();
    for (int k = 0; k < 100000; ++k) {
        add_n_builtin(a.data(), b.data(), r.data(), N);
    }
    auto end = std::chrono::high_resolution_clock::now();
    auto ns_builtin = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();
    std::cout << "GNU builtin: " << ns_builtin << " ns\n";

    // Benchmark GNU ov version
    start = std::chrono::high_resolution_clock::now();
    for (int k = 0; k < 100000; ++k) {
        add_n_builtin_ov(a.data(), b.data(), r.data(), N);
    }
    end = std::chrono::high_resolution_clock::now();
    auto ns_builtin_ov = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();
    std::cout << "GNU ov     : " << ns_builtin_ov << " ns\n";

    // Benchmark 64-bit version
    start = std::chrono::high_resolution_clock::now();
    for (int k = 0; k < 100000; ++k) {
        add_n_64bit(a.data(), b.data(), r.data(), N);
    }
    end = std::chrono::high_resolution_clock::now();
    auto ns_64bit = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();
    std::cout << "64-bit sum : " << ns_64bit << " ns\n";

    return 0;
}
