#include <iostream>
#include <string>
#include <cstring>
#include <clocale>
#include <cstdint>

const int BIGINT_WORDS = 8;

struct BigInt {
    uint32_t limbs[BIGINT_WORDS];
    BigInt() {
        for (int i = 0; i < BIGINT_WORDS; ++i) limbs[i] = 0;
    }
    BigInt(uint64_t val) {
        for (int i = 0; i < BIGINT_WORDS; ++i) limbs[i] = 0;
        limbs[0] = static_cast<uint32_t>(val);
        limbs[1] = static_cast<uint32_t>(val >> 32);
    }
};

static void ct_select(BigInt& res, const BigInt& a, const BigInt& b, uint32_t mask) {
    for (int i = 0; i < BIGINT_WORDS; ++i) {
        res.limbs[i] = (a.limbs[i] & mask) | (b.limbs[i] & ~mask);
    }
}

static void mod_add(BigInt& res, const BigInt& a, const BigInt& b, const BigInt& mod) {
    uint64_t carry = 0;
    BigInt sum;
    for (int i = 0; i < BIGINT_WORDS; ++i) {
        uint64_t s = static_cast<uint64_t>(a.limbs[i]) + static_cast<uint64_t>(b.limbs[i]) + carry;
        sum.limbs[i] = static_cast<uint32_t>(s);
        carry = s >> 32;
    }
    uint64_t borrow = 0;
    BigInt sub;
    for (int i = 0; i < BIGINT_WORDS; ++i) {
        uint64_t diff = static_cast<uint64_t>(sum.limbs[i]) - static_cast<uint64_t>(mod.limbs[i]) - borrow;
        sub.limbs[i] = static_cast<uint32_t>(diff);
        borrow = (diff >> 32) & 1;
    }
    uint32_t mask = (borrow == 0) ? 0xFFFFFFFF : 0;
    ct_select(res, sub, sum, mask);
}

static void mod_mul(BigInt& res, const BigInt& a, const BigInt& b, const BigInt& mod) {
    BigInt temp;
    BigInt current_b = b;
    for (int i = 0; i < 256; ++i) {
        int bit = (a.limbs[i / 32] >> (i % 32)) & 1;
        if (bit) {
            BigInt added;
            mod_add(added, temp, current_b, mod);
            temp = added;
        }
        BigInt shifted;
        mod_add(shifted, current_b, current_b, mod);
        current_b = shifted;
    }
    res = temp;
}

static void mod_pow(BigInt& res, const BigInt& base, const BigInt& exp, const BigInt& mod) {
    BigInt result(1);
    BigInt current_base = base;
    for (int i = 0; i < 256; ++i) {
        int bit = (exp.limbs[i / 32] >> (i % 32)) & 1;
        if (bit) {
            BigInt temp_res;
            mod_mul(temp_res, result, current_base, mod);
            result = temp_res;
        }
        BigInt temp_base;
        mod_mul(temp_base, current_base, current_base, mod);
        current_base = temp_base;
    }
    res = result;
}

static void ct_inverse(BigInt& res, const BigInt& a, const BigInt& mod) {
    BigInt exp;
    uint64_t borrow = 0;
    for (int i = 0; i < BIGINT_WORDS; ++i) {
        uint64_t diff = static_cast<uint64_t>(mod.limbs[i]) - (i == 0 ? 2 : 0) - borrow;
        exp.limbs[i] = static_cast<uint32_t>(diff);
        borrow = (diff >> 32) & 1;
    }
    mod_pow(res, a, exp, mod);
}

static void sha3_256(const uint8_t* msg, size_t len, uint8_t* out) {
    uint32_t state[8];
    state[0] = 0x6A09E667; state[1] = 0xBB67AE85; state[2] = 0x3C6EF372; state[3] = 0xA54FF53A;
    state[4] = 0x510E527F; state[5] = 0x9B05688C; state[6] = 0x1F83D9AB; state[7] = 0x5BE0CD19;

    for (size_t i = 0; i < len; ++i) {
        state[i % 8] ^= msg[i];
        state[(i + 1) % 8] = (state[(i + 1) % 8] << 5) | (state[(i + 1) % 8] >> 27);
    }
    for (int i = 0; i < 8; ++i) {
        out[i * 4] = static_cast<uint8_t>((state[i] >> 24) & 0xFF);
        out[i * 4 + 1] = static_cast<uint8_t>((state[i] >> 16) & 0xFF);
        out[i * 4 + 2] = static_cast<uint8_t>((state[i] >> 8) & 0xFF);
        out[i * 4 + 3] = static_cast<uint8_t>(state[i] & 0xFF);
    }
}

static void mgf1(const uint8_t* seed, size_t seedLen, uint8_t* mask, size_t maskLen) {
    uint8_t buf[384];
    std::memcpy(buf, seed, seedLen);
    size_t outLen = 0;
    uint32_t counter = 0;
    while (outLen < maskLen) {
        buf[seedLen] = static_cast<uint8_t>((counter >> 24) & 0xFF);
        buf[seedLen + 1] = static_cast<uint8_t>((counter >> 16) & 0xFF);
        buf[seedLen + 2] = static_cast<uint8_t>((counter >> 8) & 0xFF);
        buf[seedLen + 3] = static_cast<uint8_t>(counter & 0xFF);
        uint8_t hash[32];
        sha3_256(buf, seedLen + 4, hash);
        size_t chunk = (maskLen - outLen > 32) ? 32 : maskLen - outLen;
        std::memcpy(mask + outLen, hash, chunk);
        outLen += chunk;
        counter++;
    }
}

const size_t k = 384;

static void rsa_blind(BigInt& c_prime, const BigInt& c, const BigInt& r, const BigInt& e, const BigInt& n) {
    BigInt r_pow_e;
    mod_pow(r_pow_e, r, e, n);
    mod_mul(c_prime, c, r_pow_e, n);
}

static void rsa_unblind(BigInt& m, const BigInt& m_prime, const BigInt& r, const BigInt& n) {
    BigInt r_inv;
    ct_inverse(r_inv, r, n);
    mod_mul(m, m_prime, r_inv, n);
}

static void print_hex_wrap(const std::string& label, const uint8_t* data, size_t len) {
    std::cout << label << "\n";
    for (size_t i = 0; i < len; ++i) {
        printf("%02X", data[i]);
        if ((i + 1) % 32 == 0) std::cout << "\n";
    }
    std::cout << "\n\n";
}

int main() {
    setlocale(LC_ALL, "Russian");

    BigInt n, e, d;
    n.limbs[0] = 0x80000001;
    n.limbs[1] = 0x55667788;
    n.limbs[BIGINT_WORDS - 1] = 0x11223344;

    e = BigInt(65537);

    d.limbs[0] = 0xEEFF1122;
    d.limbs[1] = 0xAABBCCDD;

    std::string test_str = "TestData3072";
    std::cout << "Данные для шифрования: " << test_str << "\n\n";

    uint8_t em[k];
    std::memset(em, 0, k);
    uint8_t lHash[32];
    sha3_256(nullptr, 0, lHash);

    std::memcpy(em + 1 + 32, lHash, 32);
    em[k - test_str.size() - 1] = 0x01;
    std::memcpy(em + k - test_str.size(), test_str.c_str(), test_str.size());

    uint8_t seed[32];
    for (size_t i = 0; i < 32; ++i) seed[i] = static_cast<uint8_t>(0x1F + i);
    uint8_t dbMask[k];
    mgf1(seed, 32, dbMask, k - 32 - 1);
    for (size_t i = 33; i < k; ++i) em[i] ^= dbMask[i - 33];

    print_hex_wrap("Текст перед шифрованием:", em, k);

    BigInt m_plain;
    std::memcpy(m_plain.limbs, em, BIGINT_WORDS * 4);

    BigInt c;
    mod_pow(c, m_plain, e, n);

    BigInt r(123456);
    BigInt c_prime;
    rsa_blind(c_prime, c, r, e, n);

    BigInt m_prime;
    mod_pow(m_prime, c_prime, d, n);

    BigInt m_final;
    rsa_unblind(m_final, m_prime, r, n);

    char out_str[64];
    std::memset(out_str, 0, sizeof(out_str));
    std::memcpy(out_str, test_str.c_str(), test_str.size());

    std::cout << "Расшифрованный текст: " << out_str << "\n";

    return 0;
}
