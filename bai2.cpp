#include <iostream>
#include <string>
#include <algorithm>
#include <cctype>
#include <cstdio>

#define BI_BIT 1024
#include "bigint.h"

using namespace std;

// Chuyển bui thành hex little‑endian
string bui_to_hex_le(const bui& x) {
    string full = bui_to_hex(x, false);
    string hex;
    hex.reserve(full.size());
    for (char c : full) {
        if (!isspace((unsigned char)c))
            hex.push_back(c);
    }
    size_t pos = 0;
    while (pos < hex.size() && hex[pos] == '0') ++pos;
    string trimmed = (pos == hex.size()) ? string("0") : hex.substr(pos);

    for (char &c : trimmed)
        c = (char)toupper((unsigned char)c);
    reverse(trimmed.begin(), trimmed.end());
    return trimmed;
}

int main(int argc, char* argv[]) {
    if (argc != 3) {
        return 1;
    }

    if (!freopen(argv[1], "r", stdin)) return 1;
    if (!freopen(argv[2], "w", stdout)) return 1;

    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    bui p = read_bui_le();
    bui q = read_bui_le();
    bui e = read_bui_le();

    bui one = bui1();
    bui p1 = sub(p, one);
    bui q1 = sub(q, one);

    bul phi2 = mul(p1, q1);
    bui phi = bul_low(phi2);

    bui d;
    // Tìm d sao cho e*d ≡ 1 (mod phi), nếu không tồn tại thì in -1
    if (!mod_inverse(e, phi, d)) {
        cout << "-1\n";
        return 0;
    }

    cout << bui_to_hex_le(d) << "\n";
    return 0;
}
