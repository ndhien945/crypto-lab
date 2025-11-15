#include <iostream>
#include <string>
#include <algorithm>
#include <cctype>
#include <cstdio>
#include "BigInt.h"
using namespace std;

string normalize_hex_le_to_be(string s) {
    string hex;
    for (char c : s) {
        if (!isspace((unsigned char)c))
            hex.push_back(c);
    }
    if (hex.empty()) return string("0");
    reverse(hex.begin(), hex.end());
    return hex;
}

bui read_bui_le() {
    string line;
    getline(cin, line);
    string be_hex = normalize_hex_le_to_be(line);
    return bui_from_hex(be_hex);     
}

string bui_to_hex_le(const bui& x) {
    string full = bui_to_hex(x, false);
    string hex;
    for (char c : full) {
        if (!isspace((unsigned char)c))
            hex.push_back(c);
    }
    size_t pos = 0;
    while (pos < hex.size() && hex[pos] == '0') ++pos;
    string trimmed = (pos == hex.size()) ? string("0") : hex.substr(pos);

    for (char& c : trimmed)
        c = (char)toupper((unsigned char)c);

    reverse(trimmed.begin(), trimmed.end());
    return trimmed;
}

int main(int argc, char* argv[]) {
    if (argc != 3) {
        return 1;
    }

    if (!freopen(argv[1], "r", stdin))  return 1;
    if (!freopen(argv[2], "w", stdout)) return 1;

    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    bui N = read_bui_le();
    bui k = read_bui_le();
    bui x = read_bui_le();

    bui y = pow_mod(x, k, N);

    cout << bui_to_hex_le(y) << "\n";
    return 0;
}
