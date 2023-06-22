#ifndef INTT_ARITH_NAIDIV_HPP
# define INTT_ARITH_NAIDIV_HPP
# pragma once

#include "arith.hpp"

namespace ar
{ // provides naive implementations of div

template <std::unsigned_integral T, std::size_t N>
constexpr auto hwmul(array_t<T, N> const& a, H<T> const k) noexcept
{
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T>, hwbits = wbits / 2 };

  using D = D<T>;
  using H = H<T>;

  array_t<T, N> r{};

  if constexpr(std::is_same_v<T, std::uintmax_t>)
  { // multiplying half-words, wbits per iteration
    [&]<auto ...S>(std::index_sequence<S...>) noexcept
    {
      (
        [&]() noexcept
        {
          T const pp(
            T(k) * H(a[S / 2] >> (S % 2 ? std::size_t(hwbits) : 0))
          );

          if constexpr((S % 2) && (M - 1 == S))
          {
            add<S / 2>(r, array_t<T, N>{pp << hwbits});
          }
          else if constexpr(S % 2)
          {
            add<S / 2>(r, array_t<T, N>{pp << hwbits, pp >> hwbits});
          }
          else
          {
            add<S / 2>(r, array_t<T, N>{pp});
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
          D const pp(D(k) * a[S]);

          if constexpr(N - 1 == S)
          {
            add<S>(r, array_t<T, N>{T(pp)});
          }
          else
          {
            add<S>(r, array_t<T, N>{T(pp), T(pp >> wbits)});
          }
        }(),
        ...
      );
    }(std::make_index_sequence<N>());
  }

  return r;
}

template <bool Rem = false, std::unsigned_integral T, std::size_t N>
constexpr void seqdiv(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T>, bits = wbits * N };

  // Na = Nq + Nb; Nq = Na - Nb = N * wbits - CA - (N * wbits - CB) = CB - CA
  if (auto const CA(clz(a)), CB(clz(b)); CB >= CA) [[likely]]
  {
    array_t<T, M> r;
    copy(r, a);
    clear(a);
    auto i(CB - CA + 1);
    lshl(r, bits - i);

    array_t<T, M> D;
    rcopy<M - 1>(D, b);

    do
    {
      if (--i; ucmp(rlshl<1>(r), D) >= 0)
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
}

template <bool Rem = false, std::unsigned_integral T, std::size_t N>
constexpr void naidiv(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{ // wbits per iteration
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T>, hwbits = wbits / 2 };
  enum : T { dmax = (T(1) << hwbits) - 1 };

  if (auto const CA(clz(a)), CB(clz(b)); CB >= CA) [[likely]]
  {
    array_t<T, M> A;
    copy(A, a);
    clear(a);
    lshl(A, CB);

    array_t<T, M> B;
    rcopy<M - 1>(B, b);
    lshl(B, CB);

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
}

}

#endif // INTT_ARITH_NAIDIV_HPP
