#include "src/kautz.hh"

#include <cassert>
#include <cstdlib>
#include <iostream>

int main(int argc, char** argv) {
  assert(argc == 3);
  oput_graphviz_kautz(std::cout, atoi(argv[1]), atoi(argv[2]));
  return 0;
}

