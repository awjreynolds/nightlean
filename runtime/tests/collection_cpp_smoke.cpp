#include "noctium_native.h"

#include <cassert>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <vector>

static std::vector<uint8_t> read(const char *path) {
  std::ifstream source(path, std::ios::binary);
  assert(source);
  return {std::istreambuf_iterator<char>(source), std::istreambuf_iterator<char>()};
}

int main(int argc, char **argv) {
  assert(argc == 5);
  const auto request = read(argv[1]);
  const auto plan = read(argv[2]);
  const auto snapshot = read(argv[3]);
  uint64_t token = 99;
  const int32_t status = noctium_ledger_collection_page(
      request.data(), request.size(), plan.data(), plan.size(),
      snapshot.data(), snapshot.size(), &token);
  assert(status == std::stoi(argv[4]));
  if (status != NOCTIUM_NATIVE_OK) {
    assert(token == 0);
    return 0;
  }
  size_t length = 0;
  assert(noctium_native_result_length(token, &length) == NOCTIUM_NATIVE_OK);
  std::vector<uint8_t> output(length);
  size_t written = 0;
  assert(noctium_native_result_copy(token, output.data(), output.size(), &written) == NOCTIUM_NATIVE_OK);
  assert(written == length);
  assert(noctium_native_result_free(token) == NOCTIUM_NATIVE_OK);
  assert(noctium_native_result_length(token, &length) == NOCTIUM_NATIVE_INVALID_HANDLE);
  std::cout.write(reinterpret_cast<const char *>(output.data()), written);
}
