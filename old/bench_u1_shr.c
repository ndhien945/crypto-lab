#include <stdio.h>
#include <stdint.h>
#include <time.h>

typedef unsigned int u32;
#define SIZEOF_u32 (sizeof(u32) * 8)

#define N 200000000

// Branch version
static inline u32 u1_shr_branch(u32 num, u32 amnt) {
	if (amnt >= SIZEOF_u32) return 0;
	return num >> amnt;
}

// Branchless version
static inline u32 u1_shr_bl(u32 num, u32 amnt) {
	return (num >> (amnt & (SIZEOF_u32 - 1))) & -(amnt < SIZEOF_u32);
}

int main() {
	u32 sum = 0;
	clock_t start, end;

	// Test data
	u32 nums[4] = {0xFFFFFFFF, 0x12345678, 0x0F0F0F0F, 0x80000000};
	u32 shifts[4] = {0, 5, 31, 40}; // include out-of-range

	// Branch version
	start = clock();
	for (int i = 0; i < N; i++) {
		sum += u1_shr_branch(nums[i & 3], shifts[i & 3]);
	}
	end = clock();
	printf("Branch version: %f sec, sum=%u\n", (double)(end - start)/CLOCKS_PER_SEC, sum);

	sum = 0;
	// Branchless version
	start = clock();
	for (int i = 0; i < N; i++) {
		sum += u1_shr_bl(nums[i & 3], shifts[i & 3]);
	}
	end = clock();
	printf("Branchless version: %f sec, sum=%u\n", (double)(end - start)/CLOCKS_PER_SEC, sum);

	return 0;
}
