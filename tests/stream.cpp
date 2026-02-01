#include <iostream>

#include "../intt.hpp"

int main()
{
  using D = intt::intt<std::uint8_t, 3>;

  std::cout << D::min() << std::endl;;
  std::cout << D::max() << std::endl;;

  D a;
  std::cin >> a;
  std::cout << a << " error: " << !std::cin << std::endl;

  return 0;
}
