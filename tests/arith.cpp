#include <iostream>

#include "../arith.hpp"

int main()
{
  using v4ui = std::uint32_t __attribute__ ((vector_size (4 * sizeof(std::uint32_t))));

  v4ui a{1, 0, 0, 0};
  v4ui b{1, 0, 0, 0};

  ar::neg(a);
  ar::not_(a);

  ar::add(a, b);
  ar::sub(a, b);

  ar::clear(a);

  return 0;
}
