#include "../../include/noctium_native.h"

#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
#include <sys/random.h>
#include <unistd.h>

#ifdef NDEBUG
#error "Qualification requires assertions"
#endif

using Bytes = std::vector<uint8_t>;

static Bytes receive(size_t limit) {
    std::array<uint8_t, 4> length{};
    assert(std::cin.read(reinterpret_cast<char*>(length.data()), length.size()));
    uint32_t size = 0;
    for (uint8_t byte : length) size = (size << 8) | byte;
    assert(size > 0 && size <= limit);
    Bytes bytes(size);
    assert(std::cin.read(reinterpret_cast<char*>(bytes.data()), bytes.size()));
    return bytes;
}

static void send_result(uint64_t token, size_t limit) {
    size_t size = 0;
    assert(noctium_native_result_length(token, &size) == NOCTIUM_NATIVE_OK);
    assert(size > 0 && size <= limit);
    Bytes bytes(size);
    size_t copied = 0;
    assert(noctium_native_result_copy(token, bytes.data(), bytes.size(), &copied) == NOCTIUM_NATIVE_OK);
    assert(copied == size);
    assert(noctium_native_result_free(token) == NOCTIUM_NATIVE_OK);
    std::array<uint8_t, 4> length{
        uint8_t(size >> 24), uint8_t(size >> 16), uint8_t(size >> 8), uint8_t(size)
    };
    std::cout.write(reinterpret_cast<const char*>(length.data()), length.size());
    std::cout.write(reinterpret_cast<const char*>(bytes.data()), bytes.size());
    assert(std::cout.flush());
}

static void wipe(Bytes& bytes) {
    for (volatile auto& byte : bytes) byte = 0;
}

int main() {
    constexpr size_t mib = 1024 * 1024;
    const auto descriptor = receive(65536);
    auto inputs = receive(mib);
    const auto state = receive(mib);
    const auto ledger_parameters = receive(mib);
    const auto proof_parameters = receive(128 * mib);
    Bytes entropy(32);
    assert(getentropy(entropy.data(), entropy.size()) == 0);
    uint64_t owner = 0, offer = 0;
    const auto status = noctium_native_composition_owner_begin(
        descriptor.data(), descriptor.size(), inputs.data(), inputs.size(),
        state.data(), state.size(), ledger_parameters.data(), ledger_parameters.size(),
        proof_parameters.data(), proof_parameters.size(), entropy.data(), entropy.size(),
        &owner, &offer);
    wipe(inputs);
    wipe(entropy);
    if (status != NOCTIUM_NATIVE_OK) std::cerr << "owner begin returned " << status << '\n';
    assert(status == NOCTIUM_NATIVE_OK);
    send_result(offer, 4 * mib);

    auto draft = receive(16 * mib);
    uint64_t proof = 0;
    auto prove = [&](size_t slot) {
        assert(getentropy(entropy.data(), entropy.size()) == 0);
        const auto result = noctium_native_composition_owner_prove(
            owner, draft.data(), draft.size(), slot, entropy.data(), entropy.size(), &proof);
        wipe(entropy);
        return result;
    };
    assert(prove(0) == NOCTIUM_NATIVE_INVALID_RESPONSE && proof == 0);
    draft.back() ^= 1;
    assert(prove(1) == NOCTIUM_NATIVE_INVALID_RESPONSE && proof == 0);
    draft.back() ^= 1;
    assert(prove(1) == NOCTIUM_NATIVE_OK);
    send_result(proof, mib);
    assert(prove(1) == NOCTIUM_NATIVE_INVALID_STATE && proof == 0);
    assert(noctium_native_composition_owner_free(owner) == NOCTIUM_NATIVE_OK);
}
