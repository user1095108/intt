#ifndef INTT_ARITH_NAISQRT_HPP
# define INTT_ARITH_NAISQRT_HPP
# pragma once

#include "arith.hpp"

namespace ar
{ // provides naive implementations of sqrt

template <std::unsigned_integral T, std::size_t N>
constexpr void seqsqrt(array_t<T, N>& a) noexcept
{ // CR = CR + (N * wbits - CR) / 2;
  enum : std::size_t { M = 2 * N, bits = bit_size_v<decltype(a)> };

  array_t<T, M> r;
  copy(r, a);
  auto const CR((bits + clz(a)) / 2);
  lshl(r, CR);

  array_t<T, M> Q{};

  for (auto i(2 * bits - CR); bits != i;)
  {
    array_t<T, M> tmp;
    copy(tmp, Q);
    lshl<1>(tmp);
    set_bit(tmp, --i);

    if (lshl<1>(r), ucmp(r, tmp) >= 0)
    {
      sub(r, tmp);
      set_bit(Q, i);
    }
  }

  rcopy<N - 1>(a, Q);
}

}

#endif // INTT_ARITH_NAISQRT_HPP
