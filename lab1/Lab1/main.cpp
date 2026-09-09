#include <iostream>
#include <cstdint>
#include <cstring>
#include <array>
#include <clocale>
#include <cstdio>
class GaloisField {
private:
    uint16_t poly;
public:
    GaloisField(uint16_t p_x = 0x12B) : poly(p_x) {}

    uint8_t multiply(uint8_t a, uint8_t b) {
        uint8_t res = 0, temp_a = a, temp_b = b;
        for (int i = 0; i < 8; ++i) {
            res ^= (temp_a & -(temp_b & 1));
            temp_a = (temp_a << 1) ^ (-(temp_a >> 7) & (poly & 0xFF));
            temp_b >>= 1;
        }
        return res;
    }

    uint8_t inverse(uint8_t a) {
        uint8_t res = 1, t = a, e = 254;
        for (int i = 0; i < 8; ++i) {
            if (e & 1) res = multiply(res, t);
            t = multiply(t, t);
            e >>= 1;
        }
        return res & -((a != 0) & 1);
    }
};

class BeltCipher {
private:
    std::array<uint32_t, 8> round_keys;
    GaloisField gf;

    uint32_t rotl32(uint32_t v, unsigned int s) {
        return (v << (s & 31)) | (v >> (32 - (s & 31)));
    }

    uint32_t sub32(uint32_t w) {
        uint32_t res = 0;
        std::array<uint8_t, 8> matrix = { 0xF1, 0xE3, 0xC7, 0x8F, 0x1F, 0x3E, 0x7C, 0xF8 };
        for (int i = 0; i < 4; ++i) {
            uint8_t b = gf.inverse((w >> (i * 8)) & 0xFF), sbox_b = 0;
            for (int j = 0; j < 8; ++j) {
                uint8_t parity = 0, v = b & matrix[j];
                for (int k = 0; k < 8; ++k) parity ^= (v >> k) & 1;
                sbox_b |= (parity << j);
            }
            res |= static_cast<uint32_t>(sbox_b ^ 0x3A) << (i * 8);
        }
        return res;
    }

public:
    void set_key(const std::array<uint8_t, 32>& key) {
        std::memcpy(round_keys.data(), key.data(), 32);
    }

    void encrypt_block(const std::array<uint8_t, 16>& src, std::array<uint8_t, 16>& dst) {
        std::array<uint32_t, 4> x = { 0 };
        std::memcpy(x.data(), src.data(), 16);

        std::array<int, 32> k_idx = {
            0,1,2,3, 4,5,6,7, 0,1,2,3, 4,5,6,7,
            0,1,2,3, 4,5,6,7, 0,1,2,3, 4,5,6,7
        };

        for (int r = 0; r < 8; ++r) {
            int o = r * 4;
            x[0] += round_keys[k_idx[o]];
            x[2] += round_keys[k_idx[o + 1]];
            x[0] = rotl32(sub32(x[0]), 5);
            x[1] ^= x[0];
            x[2] = rotl32(sub32(x[2]), 21);
            x[3] ^= x[2];
            x[0] -= round_keys[k_idx[o + 2]];
            x[1] += round_keys[k_idx[o + 3]];
            x[1] = rotl32(sub32(x[1]), 13);
            x[0] ^= x[1];
            x[2] += x[1];
            x[3] -= x[0];
            x[3] = rotl32(sub32(x[3]), 9);
            x[2] ^= x[3];
            x[1] -= x[3];

            uint32_t tmp = x[0]; x[0] = x[1]; x[1] = x[2]; x[2] = x[3]; x[3] = tmp;
        }
        std::memcpy(dst.data(), &x[1], 4);
        std::memcpy(dst.data() + 4, &x[2], 4);
        std::memcpy(dst.data() + 8, &x[0], 4);
        std::memcpy(dst.data() + 12, &x[3], 4);
    }
};

class GcmMode {
private:
    BeltCipher cipher;
    std::array<uint8_t, 16> H;

    void multiply_gf128(std::array<uint8_t, 16>& x, const std::array<uint8_t, 16>& y) {
        std::array<uint8_t, 16> z = { 0 }, v = y;
        for (int i = 0; i < 128; ++i) {
            uint8_t bit = (x[i / 8] >> (7 - (i % 8))) & 1;
            for (int j = 0; j < 16; ++j) z[j] ^= (v[j] & -bit);
            uint8_t rem_mask = -(v[15] & 1);
            uint8_t carry = 0;
            for (int j = 0; j < 16; ++j) {
                uint8_t next_carry = v[j] & 1;
                v[j] = (v[j] >> 1) | (carry << 7);
                carry = next_carry;
            }
            v[0] ^= (rem_mask & 0xE1);
        }
        x = z;
    }

    void process_data(const uint8_t* data, size_t len, std::array<uint8_t, 16>& y) {
        size_t blocks = (len + 15) / 16;
        for (size_t i = 0; i < blocks; ++i) {
            std::array<uint8_t, 16> b = { 0 };
            size_t rem = len - i * 16;
            std::memcpy(b.data(), data + i * 16, (rem < 16) ? rem : 16);
            for (int j = 0; j < 16; ++j) y[j] ^= b[j];
            multiply_gf128(y, H);
        }
    }

public:
    void init(const std::array<uint8_t, 32>& key) {
        cipher.set_key(key);
        std::array<uint8_t, 16> zero = { 0 };
        cipher.encrypt_block(zero, H);
    }

    void encrypt(const std::array<uint8_t, 12>& iv, const uint8_t* p, size_t len,
        const uint8_t* aad, size_t aad_len, uint8_t* c, std::array<uint8_t, 16>& tag) {
        std::array<uint8_t, 16> cb = { 0 }, eco0 = { 0 }, eco = { 0 };
        std::memcpy(cb.data(), iv.data(), 12);
        cb[15] = 1;
        cipher.encrypt_block(cb, eco0);

        uint32_t counter = 2;
        for (size_t i = 0; i < (len + 15) / 16; ++i) {
            std::memcpy(cb.data(), iv.data(), 12);
            for (int j = 0; j < 4; ++j) cb[15 - j] = (counter >> (j * 8)) & 0xFF;
            counter++;
            cipher.encrypt_block(cb, eco);
            size_t rem = len - i * 16;
            size_t take = (rem < 16) ? rem : 16;
            for (size_t j = 0; j < take; ++j) c[i * 16 + j] = p[i * 16 + j] ^ eco[j];
        }

        std::array<uint8_t, 16> y = { 0 }, len_b = { 0 };
        process_data(aad, aad_len, y);
        process_data(c, len, y);

        uint64_t a_bits = static_cast<uint64_t>(aad_len) * 8;
        uint64_t c_bits = static_cast<uint64_t>(len) * 8;
        for (int j = 0; j < 8; ++j) {
            len_b[7 - j] = (a_bits >> (j * 8)) & 0xFF;
            len_b[15 - j] = (c_bits >> (j * 8)) & 0xFF;
        }
        for (int j = 0; j < 16; ++j) y[j] ^= len_b[j];
        multiply_gf128(y, H);
        for (int j = 0; j < 16; ++j) tag[j] = y[j] ^ eco0[j];
    }

    bool verify_tag(const std::array<uint8_t, 16>& t1, const std::array<uint8_t, 16>& t2) {
        uint8_t d = 0;
        for (int i = 0; i < 16; ++i) d |= (t1[i] ^ t2[i]);
        return d == 0;
    }
};

int main() {
    setlocale(LC_ALL, "Russian"); 

    std::array<uint8_t, 32> key = {
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,0x10,
        0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,
        0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,0x20
    };
    std::array<uint8_t, 12> iv = {
        0xAA,0xBB,0xCC,0xDD,0xEE,0xFF,0x00,0x11,0x22,0x33,0x44,0x55
    };

    uint8_t p[] = "Hello, BelT-GCM 4 Variant";
    uint8_t aad[] = "BresTU 2026";
    uint8_t c[25] = { 0 };
    std::array<uint8_t, 16> tag = { 0 };

    GcmMode gcm;
    gcm.init(key);
    gcm.encrypt(iv, p, 25, aad, 11, c, tag);

    std::cout << "--- Ðåæèì ÁåëÒ-GCM ---" << std::endl;

    std::cout << "Øèôðîòåêñò (HEX): ";
    for (int i = 0; i < 25; ++i) {
        printf("%02X ", c[i]);
    }
    std::cout << std::endl;

    std::cout << "Èìèòîâñòàâêà Tag (HEX): ";
    for (int i = 0; i < 16; ++i) {
        printf("%02X ", tag[i]);
    }
    std::cout << std::endl;

    return 0;
}


