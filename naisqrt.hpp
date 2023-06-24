#ifndef INTT_ARITH_NAISQRT_HPP
# define INTT_ARITH_NAISQRT_HPP
# pragma once

#include "arith.hpp"

namespace ar
{ // provides naive implementations of sqrt

constexpr auto&& seqsqrt(auto&& a) noexcept
{ // CR = CR + (N * wbits - CR) / 2;
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

  enum : std::size_t { M = 2 * N, bits = bit_size_v<decltype(a)> };

  array_t<T, M> r;
  auto const CR((bits + clz(a)) / 2);
  lshl(copy(r, a), CR);

  array_t<T, M> Q{};

  for (auto i(2 * bits - CR); bits != i;)
  {
    if (auto tmp(Q); set_bit(lshl<1>(tmp), --i), ucmp(lshl<1>(r), tmp) >= 0)
    {
      sub(r, tmp);
      set_bit(Q, i);
    }
  }

  return rcopy<N - 1>(a, Q);
}

}

#endif // INTT_ARITH_NAISQRT_HPP
