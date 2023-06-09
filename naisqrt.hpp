#ifndef INTT_ARITH_NAISQRT_HPP
# define INTT_ARITH_NAISQRT_HPP
# pragma once

#include "arith.hpp"

namespace ar
{ // provides naive implementations of sqrt

template <std::unsigned_integral T, std::size_t N>
constexpr auto seqsqrt(T (&a)[N]) noexcept
{ // CR = CR + (N * wbits - CR) / 2;
  T r[2 * N], Q[2 * N]{};
  copy(r, a);

  enum : std::size_t { bits = bit_size_v<decltype(a)> };

  auto const CR((bits + clz(a)) / 2);
  lshl(r, CR);

  for (auto i(2 * bits - CR); bits != i;)
  {
    lshl<1>(r);

    T tmp[2 * N];
    copy(tmp, Q);
    lshl<1>(tmp);

    if (set_bit(tmp, --i), ucmp(r, tmp) >= 0)
    {
      set_bit(Q, i);
      sub(r, tmp);
    }
  }

  rcopy<N - 1>(a, Q);
}

}

#endif // INTT_ARITH_NAISQRT_HPP
