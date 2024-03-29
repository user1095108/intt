#ifndef INTT_ARITH_NAISQRT_HPP
# define INTT_ARITH_NAISQRT_HPP
# pragma once

#include "arith.hpp"

namespace ar
{ // provides naive implementations of sqrt

constexpr auto&& seqsqrt(uarray_c auto&& a) noexcept
{ // CR = CR + (N * wbits - CR) / 2;
  using T = std::remove_cvref_t<decltype(a[0])>;

  enum : std::size_t { N = size<decltype(a)>(), M = 2 * N };
  enum : std::size_t { bits = bit_size_v<decltype(a)> };

  array_t<T, M> r;
  auto const CR((bits + clz(a)) / 2);
  lshl(copy(r, a), CR);

  array_t<T, M> Q{};

  for (auto i(2 * bits - CR); bits != i;)
  {
    if (ucmp(lshl<1>(r), set_bit(lshl<1>(Q), --i)) >= 0)
    {
      sub(r, Q);
      set_bit(lshr<1>(clear_bit(Q, i)), i);
    }
    else
    {
      lshr<1>(clear_bit(Q, i));
    }
  }

  //
  return rcopy<N - 1>(a, Q);
}

}

#endif // INTT_ARITH_NAISQRT_HPP
