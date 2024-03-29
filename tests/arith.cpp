#include <iostream>

#include "../naidiv.hpp"
#include "../naimul.hpp"
#include "../naisqrt.hpp"

int main()
{
  {
    unsigned a[4]{1};
    unsigned b[4]{1};

    ar::naidiv(a, b);
    ar::add(a, b);
    ar::naimul(a, b);
  }

  {
    using v4ui = std::uint32_t __attribute__ ((vector_size (4 * sizeof(std::uint32_t))));

    v4ui a{1, 0, 0, 0};
    v4ui b{1, 0, 0, 0};

    ar::neg(a);
    ar::not_(a);

    ar::add(a, b);
    ar::sub(a, b);

    ar::seqsqrt(a);

    ar::clear(a);
  }

  return 0;
}
