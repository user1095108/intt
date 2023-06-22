#ifndef INTT_ARITH_NAIMUL_HPP
# define INTT_ARITH_NAIMUL_HPP
# pragma once

#include "arith.hpp"

namespace ar
{ // provides naive implementations of mul

template <std::unsigned_integral T, std::size_t N>
constexpr void seqmul(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T> };

  array_t<T, M> A;
  rcopy<M - 1>(A, a);

  array_t<T, M> r{};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      [&]() noexcept
      {
        if (test_bit<I>(b)) add(r, A);

        lshr<1>(r);
      }(),
      ...
    );
  }(std::make_index_sequence<wbits * N>());

  //
  copy(a, r);
}

template <std::unsigned_integral T, std::size_t N>
constexpr void naimul(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  array_t<T, N> r{};

  if constexpr(std::is_same_v<T, std::uintmax_t>)
  { // multiplying half-words, wbits per iteration
    enum : std::size_t { M = 2 * N, hwbits = wbits / 2 };

    for (std::size_t i{}; M != i; ++i)
    { // bit_size_v<H> * (i + j) < wbits * N
      auto S(i);

      do
      {
        auto const j(S - i);

        T const pp(T(H<T>(a[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0))) *
          H<T>(b[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0)));

        S % 2 ?
          add(r, array_t<T, 2>{pp << hwbits, pp >> hwbits}, S / 2) :
          add(r, array_t<T, 1>{pp}, S / 2);
      }
      while (M != ++S);
    }
  }
  else
  { // multiplying words, 2 * wbits per iteration
    for (std::size_t i{}; N != i; ++i)
    { // bit_size_v<T> * (i + j) < bit_size_v<T> * N
      auto S(i);

      do
      {
        D<T> const pp(D<T>(a[i]) * b[S - i]);

        add(r, array_t<T, 2>{T(pp), T(pp >> wbits)}, S);
      }
      while (N != ++S);
    }
  }

  //
  copy(a, r);
}

}

#endif // INTT_ARITH_MUL_HPP
