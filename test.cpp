#define CIGINT_IMPLEMENTATION
#define CIGINT_STRIP_PREFIX
#define CIGINT_N (512 / 32)
// bench_shifts.cpp
#define CIGINT_IMPLEMENTATION
#include <chrono>
#include <cmath>
#include <random>
#include <cstring>
#include <cassert>
#include <iostream>
#include "cigint.h"

using u32 = uint32_t;
static inline uint64_t now_ns() {
  using namespace std::chrono;
  return duration_cast<nanoseconds>(steady_clock::now().time_since_epoch()).count();
}

// -------- Two-phase versions (shl2/shr2) --------

Cigint shl2(Cigint lhs, uint amnt) {
  Cigint res = (Cigint){0};
  size_t limb_off = amnt / SIZEOF_UINT;
  size_t bits = amnt % SIZEOF_UINT;
  if (limb_off >= CIGINT_N) return res;

  if (bits == 0) {
    for (size_t i = 0; i + limb_off < CIGINT_N; ++i)
      res.data[i] = lhs.data[i + limb_off];
    return res;
  }
  size_t rbits = SIZEOF_UINT - bits;
  size_t i = 0;
  for (; i + limb_off + 1 < CIGINT_N; ++i)
    res.data[i] = (lhs.data[i + limb_off] << bits) |
                  (lhs.data[i + limb_off + 1] >> rbits);
  if (i + limb_off < CIGINT_N)
    res.data[i] = (lhs.data[i + limb_off] << bits);
  return res;
}

Cigint shr2(Cigint lhs, uint amnt) {
  Cigint res = (Cigint){0};
  size_t limb_off = amnt / SIZEOF_UINT;
  size_t bits = amnt % SIZEOF_UINT;
  if (limb_off >= CIGINT_N) return res;

  if (bits == 0) {
    for (size_t i = 0; i + limb_off < CIGINT_N; ++i)
      res.data[CIGINT_N - 1 - i] = lhs.data[CIGINT_N - 1 - (i + limb_off)];
    return res;
  }
  size_t lbits = SIZEOF_UINT - bits;
  size_t i = 0;
  for (; i + limb_off + 1 < CIGINT_N; ++i) {
    uint hi = lhs.data[CIGINT_N - 1 - (i + limb_off)];
    uint lo = lhs.data[CIGINT_N - 1 - (i + limb_off + 1)];
    res.data[CIGINT_N - 1 - i] = (hi >> bits) | (lo << lbits);
  }
  if (i + limb_off < CIGINT_N) {
    uint hi = lhs.data[CIGINT_N - 1 - (i + limb_off)];
    res.data[CIGINT_N - 1 - i] = (hi >> bits);
  }
  return res;
}

// static inline Cigint shl2(Cigint lhs, uint amnt) {
//   Cigint res = lhs;                      // keep as you wrote it
//   size_t i = 0;
//
//   const size_t offset = amnt / SIZEOF_UINT;        // FIX: floor, not ceil
//   const size_t bits   = amnt % SIZEOF_UINT;        // intra-word
//   const size_t n      = (offset < CIGINT_N) ? (CIGINT_N - offset) : 0;
//
//   if (n == 0) {                          // everything shifted out
//     while (i < CIGINT_N) { res.data[i] = 0u; i++; }
//     return res;
//   }
//
//   if (bits == 0) {
//     /* PURE LIMB MOVE: res[i] = lhs[i+offset] ; tail zeroed  */
//     while (i < n) {
//       res.data[i] = lhs.data[i + offset];
//       i++;
//     }
//     while (i < CIGINT_N) {
//       res.data[i] = 0u;
//       i++;
//     }
//     return res;
//   }
//
//   /* GENERAL CASE (bits != 0):
//      first, stitches where both sources exist:
//        res[i] = (lhs[i+offset] << bits) | (lhs[i+offset+1] >> (W - bits))
//      for i = 0 .. n-2   (so i+offset+1 is in range)
//   */
//   while (i + 1 < n) {
//     size_t s0 = i + offset;
//     size_t s1 = s0 + 1;
//     res.data[i] = lhs.data[s0] << bits |
//       lhs.data[s1] >> (SIZEOF_UINT - bits);
//     i++;
//   }
//
//   /* boundary element i == n-1: only the hi part remains */
//   if (i < n) {
//     size_t s0 = i + offset;
//     res.data[i] = lhs.data[s0] << bits;
//     i++;
//   }
//
//   /* tail is shifted out -> zero */
//   while (i < CIGINT_N) {
//     res.data[i] = 0u;
//     i++;
//   }
//
//   return res;
// }
//
// static inline Cigint shl2a(Cigint lhs, uint amnt) {
//   Cigint res = lhs;
//   size_t i = 0;
//   size_t offset = (amnt + SIZEOF_UINT - 1) / SIZEOF_UINT;
//   size_t rshift_amnt = SIZEOF_UINT - (amnt % SIZEOF_UINT);
//   while (i < CIGINT_N - offset) {
//     res.data[i] = u1_shl(lhs.data[i], amnt);
//     res.data[i] |= u1_shr(lhs.data[i + offset], rshift_amnt);
//     i++;
//   }
//   while (i < CIGINT_N) {
//     res.data[i] = u1_shl(lhs.data[i], amnt);
//     i++;
//   }
//   return res;
// }
//
// // static inline Cigint shl2(Cigint lhs, uint amnt) {
// //   if (!amnt) return lhs;
// //   const size_t limb_off = amnt / SIZEOF_UINT;
// //   const u32 bits = amnt % SIZEOF_UINT;
// //   Cigint r = {0};
// //   if (limb_off >= CIGINT_N) return r;
// //
// //   const size_t n = CIGINT_N - limb_off;
// //   if (limb_off == 0) {
// //     std::memcpy(&r.data[0], &lhs.data[0], n * sizeof(u32));
// //   } else {
// //     std::memmove(&r.data[0], &lhs.data[limb_off], n * sizeof(u32));
// //   }
// //   if (bits) {
// //     u32 snap[CIGINT_N];
// //     std::memcpy(snap, r.data, sizeof snap);
// //     for (size_t i = 0; i < CIGINT_N; ++i) {
// //       u32 hi = (u32)(snap[i] << bits);
// //       u32 lo = (i + 1 < CIGINT_N) ? (u32)(snap[i + 1] >> (SIZEOF_UINT - bits)) : 0u;
// //       r.data[i] = hi | lo;
// //     }
// //   }
// //   return r;
// // }
//
// static inline Cigint shr2(Cigint lhs, uint amnt) {
//   if (!amnt) return lhs;
//   const size_t limb_off = amnt / SIZEOF_UINT;
//   const u32 bits = amnt % SIZEOF_UINT;
//   Cigint r = {0};
//   if (limb_off >= CIGINT_N) return r;
//
//   const size_t n = CIGINT_N - limb_off;
//   if (limb_off == 0) {
//     std::memcpy(&r.data[0], &lhs.data[0], n * sizeof(u32));
//   } else {
//     std::memmove(&r.data[limb_off], &lhs.data[0], n * sizeof(u32));
//   }
//   if (bits) {
//     u32 snap[CIGINT_N];
//     std::memcpy(snap, r.data, sizeof snap);
//     for (size_t i = 0; i < CIGINT_N; ++i) {
//       u32 lo = (u32)(snap[i] >> bits);
//       u32 hi = (i > 0) ? (u32)(snap[i - 1] << (SIZEOF_UINT - bits)) : 0u;
//       r.data[i] = hi | lo;
//     }
//   }
//   return r;
// }

// -------- Single-pass corrected baseline (shl1/shr1) --------
// static inline Cigint shl1(Cigint x, uint amnt) {
//   if (!amnt) return x;
//   const size_t limb_off = amnt / SIZEOF_UINT;
//   const u32 bits = amnt % SIZEOF_UINT;
//   Cigint r = {0};
//   for (size_t i = 0; i < CIGINT_N; ++i) {
//     size_t src = i + limb_off;
//     if (src >= CIGINT_N) continue;
//     u32 v = x.data[src];
//     r.data[i] |= bits ? (u32)(v << bits) : v;
//     if (bits && src + 1 < CIGINT_N)
//       r.data[i] |= (u32)(x.data[src + 1] >> (SIZEOF_UINT - bits));
//   }
//   return r;
// }
// static inline Cigint shr1(Cigint x, uint amnt) {
//   if (!amnt) return x;
//   const size_t limb_off = amnt / SIZEOF_UINT;
//   const u32 bits = amnt % SIZEOF_UINT;
//   Cigint r = {0};
//   for (size_t i = 0; i < CIGINT_N; ++i) {
//     if (i < limb_off) continue;
//     size_t src = i - limb_off;
//     u32 v = x.data[src];
//     r.data[i] |= bits ? (u32)(v >> bits) : v;
//     if (bits && src > 0)
//       r.data[i] |= (u32)(x.data[src - 1] << (SIZEOF_UINT - bits));
//   }
//   return r;
// }

// -------- Your old buggy versions (optional) --------
// Keep only if you want to see them fail correctness on word-multiple shifts.
static inline Cigint shl_old(Cigint lhs, uint amnt) {
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
static inline Cigint shr_old(Cigint lhs, uint amnt) {
  Cigint res = lhs;
  size_t i = 0;
  size_t offset = (amnt + SIZEOF_UINT - 1) / SIZEOF_UINT;
  size_t bits_amnt = amnt % SIZEOF_UINT;
  size_t lshift_amnt = SIZEOF_UINT - bits_amnt;
  while (i < CIGINT_N - offset) {
    res.data[CIGINT_N - 1 - i] = u1_shr(lhs.data[CIGINT_N - 1 - i], amnt);
    uint last_bits = u1_get_last_nbits(lhs.data[CIGINT_N - 1 - i - offset], bits_amnt);
    res.data[CIGINT_N - 1 - i] |= u1_shl(last_bits, lshift_amnt);
    i++;
  }
  while (i < CIGINT_N) {
    res.data[CIGINT_N - 1 - i] = u1_shr(lhs.data[CIGINT_N - 1 - i], amnt);
    i++;
  }
  return res;
}

// ----- helpers -----
static inline bool eq(const Cigint& a, const Cigint& b) {
  for (size_t i=0;i<CIGINT_N;++i) if (a.data[i]!=b.data[i]) return false;
  return true;
}

int main(){
  std::mt19937_64 rng(12345);
  auto rand_cig = [&]{
    Cigint x = {0};
    for (size_t i=0;i<CIGINT_N;++i) x.data[i] = (u32)rng();
    // ensure non-zero LSW sometimes
    x.data[CIGINT_N-1] |= 1u;
    return x;
  };

  const int ITERS = 20000;
  uint64_t t_shl2=0, t_shl1=0, t_shl_old=0;
  uint64_t t_shr2=0, t_shr1=0, t_shr_old=0;

  // correctness + warmup
  for (int i=0;i<2000;++i){
    auto x = rand_cig();
    uint sh = (uint)(rng() % (CIGINT_N * SIZEOF_UINT));
    // auto a = shl2(x,sh), b = shl1(x,sh);
    // assert(eq(a,b)); // must match
    // auto c = shr2(x,sh), d = shr1(x,sh);
    // assert(eq(c,d)); // must match
  }

  // measure
  for (int i=0;i<ITERS;++i){
    auto x = rand_cig();
    uint sh = (uint)(rng() % (CIGINT_N * SIZEOF_UINT));

    auto t0=now_ns(); volatile auto a=shl2(x,sh); (void)a; auto t1=now_ns(); t_shl2 += (t1-t0);
    // t0=now_ns(); volatile auto b=shl1(x,sh); (void)b; t1=now_ns(); t_shl1 += (t1-t0);
    t0=now_ns(); volatile auto c=shr2(x,sh); (void)c; t1=now_ns(); t_shr2 += (t1-t0);
    // t0=now_ns(); volatile auto d=shr1(x,sh); (void)d; t1=now_ns(); t_shr1 += (t1-t0);

    // Optional: old buggy timings (don’t assert equality, they can be wrong)
    sh += 1;
    t0=now_ns(); volatile auto e=shl_old(x,sh); (void)e; t1=now_ns(); t_shl_old += (t1-t0);
    t0=now_ns(); volatile auto f=shr_old(x,sh); (void)f; t1=now_ns(); t_shr_old += (t1-t0);
  }

  std::cout << "avg ns/op (lower is better)\n";
  std::cout << "SHL two-phase: " << (t_shl2/ITERS) << "\n";
  // std::cout << "SHL 1-pass   : " << (t_shl1/ITERS) << "\n";
  std::cout << "SHL old (bug): " << (t_shl_old/ITERS) << " (not reliable)\n";
  std::cout << "SHR two-phase: " << (t_shr2/ITERS) << "\n";
  // std::cout << "SHR 1-pass   : " << (t_shr1/ITERS) << "\n";
  std::cout << "SHR old (bug): " << (t_shr_old/ITERS) << " (not reliable)\n";
}

// avg ns/op (lower is better)
// SHL two-phase: 90
// SHL 1-pass   : 93
// SHL old (bug): 99 (not reliable)
// SHR two-phase: 89
// SHR 1-pass   : 100
// SHR old (bug): 111 (not reliable)
