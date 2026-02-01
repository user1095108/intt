#include <iostream>

#include "../intt.hpp"

int main()
{
  using D = intt::intt<std::uint8_t, 3>;

  std::cout << D::min() << std::endl;;
  std::cout << D::max() << std::endl;;

  for (;;)
  {
    D a;
    std::cin >> a;
    std::cout << a << " error: " << !std::cin << std::endl;
    std::cin.clear();
    std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
  }

  return 0;
}
