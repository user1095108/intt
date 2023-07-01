#include <iostream>

#include "../debug.hpp"
#include "../intt.hpp"

int main()
{
//using D = intt::intt<std::uint8_t, 16>;
//using D = intt::intt<std::uint16_t, 8>;
//using D = intt::intt<std::uint32_t, 4>;
  using D = intt::intt<std::uint64_t, 2>;

  std::cout << D::min() << std::endl;
  std::cout << D::max() << std::endl;

  std::cout << ar::to_raw((D(-6666666666ll) >> 1).v_) << (long long)(D(-6666666666ll) >> 1) << std::endl;
  std::cout << D(88) / D(11) << std::endl;
  std::cout << D(8) / D(10) << std::endl;

  //
  D a(-1025);
  D b(-1024);

  //
  {
    std::cout << ar::to_raw(D(-11).v_) << std::endl;
    std::cout << ar::to_raw((D(-10) + D(-1)).v_) << std::endl;
    std::cout << int(D(1) << 11) << " : " << ar::to_raw((D(1) << 11).v_) << std::endl;
    std::cout << int(D(-2) >> 1) << " : " << ar::to_raw((D(-2) >> 1).v_) << std::endl;
  }

  //
  {
    std::cout << "== " << (a == b) << std::endl;
    std::cout << "> " << (a > b) << std::endl;
    std::cout << "< " << (a < b) << std::endl;
    std::cout << int(a + b) << std::endl;
    std::cout << int(a - b) << std::endl;
  }

  //
  {
    std::cout << int(D(1049600)) << " : " << ar::to_raw(D(1049600).v_) << std::endl;
    std::cout << ar::to_raw(a.v_) << std::endl;
    std::cout << ar::to_raw(b.v_) << std::endl;
    std::cout << (a * b) << " " << ar::to_raw((a * b).v_) << std::endl;
  }

  std::cout << "div():" << std::endl;

  {
    std::cout << int(D(-123456789) / D(3)) << std::endl;
    std::cout << int(D(123456789) / D(-3)) << std::endl;
    std::cout << int(D(-123456789) / D(-3)) << std::endl;
  }

  std::cout << "misc:" << std::endl;

  {
    std::cout << (-100 % 3) << std::endl;
    std::cout << ar::to_raw(D(std::int64_t(1) << 63).v_) << std::endl;
    std::cout << (D(5) < (std::int64_t(1) << 63)) << std::endl;
    std::cout << D(12345678901.1234) << std::endl;
    std::cout << D(-12345678901.1234) << std::endl;
  }

  std::cout << "sqrt():" << std::endl;

  {
    std::cout << isqrt(D(1)) << std::endl;
    std::cout << isqrt(D(4)) << std::endl;
    std::cout << isqrt(D(9)) << std::endl;
    std::cout << isqrt(D(16)) << std::endl;
    std::cout << isqrt(D(25)) << std::endl;
  }

  {
    std::cout << intt::to_integral<D>("123456789012").first + 1 << std::endl;
  }

  //
  return 0;
}
