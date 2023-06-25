#ifndef INTT_ARITH_NAIMUL_HPP
# define INTT_ARITH_NAIMUL_HPP
# pragma once

#include "arith.hpp"

namespace ar
{ // provides naive implementations of mul

constexpr auto&& seqmul(uarray_c auto&& a, uarray_c auto const& b) noexcept
  requires(
    (size<decltype(a)>() == size<decltype(b)>()) &&
    std::is_same_v<
      std::remove_cvref_t<decltype(a[0])>,
      std::remove_cvref_t<decltype(b[0])>
    >
  )
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { N = size<decltype(a)>() };
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
  return copy(a, r);
}

constexpr auto&& naimul(uarray_c auto&& a, uarray_c auto const& b) noexcept
  requires(
    (size<decltype(a)>() == size<decltype(b)>()) &&
    std::is_same_v<
      std::remove_cvref_t<decltype(a[0])>,
      std::remove_cvref_t<decltype(b[0])>
    >
  )
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { N = size<decltype(a)>(), wbits = bit_size_v<T> };

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
  return copy(a, r);
}

}

#endif // INTT_ARITH_MUL_HPP
