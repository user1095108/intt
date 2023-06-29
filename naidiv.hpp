#ifndef INTT_ARITH_NAIDIV_HPP
# define INTT_ARITH_NAIDIV_HPP
# pragma once

#include "arith.hpp"

namespace ar
{ // provides naive implementations of div

constexpr auto hwmul(uarray_c auto const& a,
  H<std::remove_cvref_t<decltype(a[0])>> const k) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { N = size<decltype(a)>(), M = 2 * N };
  enum : std::size_t { wbits = bit_size_v<T>, hwbits = wbits / 2 };

  array_t<T, N> r{};

  if constexpr(std::is_same_v<T, std::uintmax_t>)
  { // multiplying half-words, wbits per iteration
    [&]<auto ...S>(std::index_sequence<S...>) noexcept
    {
      (
        [&]() noexcept
        {
          if constexpr(T const pp(
            T(k) * H<T>(a[S / 2] >> (S % 2 ? std::size_t(hwbits) : 0)));
            (S % 2) && (M - 1 == S))
          {
            add<S / 2>(r, array_t<T, 1>{pp << hwbits});
          }
          else if constexpr(S % 2)
          {
            add<S / 2>(r, array_t<T, 2>{pp << hwbits, pp >> hwbits});
          }
          else
          {
            add<S / 2>(r, array_t<T, 1>{pp});
          }
        }(),
        ...
      );
    }(std::make_index_sequence<M>());
  }
  else
  { // multiplying words, 2 * wbits per iteration
    [&]<auto ...S>(std::index_sequence<S...>) noexcept
    {
      (
        [&]() noexcept
        {
          if constexpr(D<T> const pp(k * D<T>(a[S])); N - 1 == S)
          {
            add<S>(r, array_t<T, 1>{T(pp)});
          }
          else
          {
            add<S>(r, array_t<T, 2>{T(pp), T(pp >> wbits)});
          }
        }(),
        ...
      );
    }(std::make_index_sequence<N>());
  }

  return r;
}

template <bool Rem = false>
constexpr auto&& seqdiv(uarray_c auto&& a, uarray_c auto const& b) noexcept
  requires(
    std::is_unsigned_v<std::remove_cvref_t<decltype(a[0])>> &&
    (size<decltype(a)>() == size<decltype(b)>()) &&
    std::is_same_v<
      std::remove_cvref_t<decltype(a[0])>,
      std::remove_cvref_t<decltype(b[0])>
    >
  )
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { N = size<decltype(a)>(), M = 2 * N };
  enum : std::size_t { wbits = bit_size_v<T>, bits = wbits * N };

  // Na = Nq + Nb; Nq = Na - Nb = N * wbits - CA - (N * wbits - CB) = CB - CA
  if (auto const CA(clz(a)), CB(clz(b)); CB >= CA) [[likely]]
  {
    array_t<T, M> r;
    auto i(CB - CA + 1);
    lshl(copy(r, a), bits - i);
    clear(a);

    array_t<T, M> D;
    rcopy<M - 1>(D, b);

    do
    {
      if (--i; ucmp(lshl<1>(r), D) >= 0)
      {
        sub(r, D);
        set_bit(a, i);
      }
    }
    while (i);

    //
    if constexpr(Rem) rcopy<N - 1>(a, r);
  }
  else if constexpr(!Rem) clear(a);

  return a;
}

template <bool Rem = false>
constexpr auto&& naidiv(uarray_c auto&& a, uarray_c auto const& b) noexcept
  requires(
    (size<decltype(a)>() == size<decltype(b)>()) &&
    std::is_same_v<
      std::remove_cvref_t<decltype(a[0])>,
      std::remove_cvref_t<decltype(b[0])>
    >
  )
{ // wbits per iteration
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { N = size<decltype(a)>(), M = 2 * N };
  enum : std::size_t { wbits = bit_size_v<T>, hwbits = wbits / 2 };
  enum : T { dmax = (T(1) << hwbits) - 1 };

  if (auto const CA(clz(a)), CB(clz(b)); CB >= CA) [[likely]]
  {
    array_t<T, M> A;
    lshl(copy(A, a), CB);
    clear(a);

    array_t<T, M> B;
    lshl(rcopy<M - 1>(B, b), CB);

    H<T> const B0(B[M - 1] >> hwbits);

    auto k(N + 1 + (CB - CA) / wbits);
    wshr(B, M - k);

    auto const correction_step([&](T d) noexcept
        {
          if (d >> hwbits) [[unlikely]] d = dmax;
          sub(A, hwmul(lshr<hwbits>(B), d));

          for (; is_neg(A); --d, add(A, B));

          return d;
        }
      );

    do
    {
      auto const h(correction_step(A[--k] / B0));

      a[k - N] = h << hwbits |
        correction_step((T(A[k] << hwbits) | T(A[k - 1] >> hwbits)) / B0);
    }
    while (N != k);

    //
    if constexpr(Rem) copy(a, lshr(A, CB));
  }
  else if constexpr(!Rem) clear(a);

  return a;
}

}

#endif // INTT_ARITH_NAIDIV_HPP
