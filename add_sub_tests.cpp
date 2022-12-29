#include <iostream>

#include "intt.hpp"

int main()
{
  using D = intt::intt<std::uint8_t, 3>;

  for (D i{D::max()}; i != D::min(); --i)
  {
    std::cout << i << std::endl;
  }

  for (D i{D::min()}; i != D::max(); ++i)
  {
    std::cout << i << std::endl;
  }

  return 0;
}
