#ifndef INTT_ARITH_NAIDIV_HPP
# define INTT_ARITH_NAIDIV_HPP
# pragma once

#include "arith.hpp"

namespace ar
{ // provides naive implementations of div

template <bool Rem = false, std::unsigned_integral T, std::size_t N>
constexpr void seqdiv(T (&a)[N], T const (&b)[N]) noexcept
{
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T>, bits = wbits * N };

  T r[M];

  // Na = Nq + Nb; Nq = Na - Nb = N * wbits - CA - (N * wbits - CB) = CB - CA
  if (auto const CA(clz(a)), CB(clz(b)); CB >= CA) [[likely]]
  {
    copy(r, a);
    clear(a);
    auto i(CB - CA + 1);
    lshl(r, bits - i);

    T D[M];
    rcopy<M - 1>(D, b);

    do
    {
      if (--i; lshl<1>(r), ucmp(r, D) >= 0)
      {
        sub(r, D);
        set_bit(a, i);
      }
    }
    while (i);
  }
  else
  {
    if constexpr(Rem) return; else clear(a);
  }

  //
  if constexpr(Rem)
  {
    rcopy<N - 1>(a, r);
  }
}

template <std::unsigned_integral T, std::size_t N>
constexpr void hwmul(T const (&a)[N], H<T> const k, T (&r)[N]) noexcept
{
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T>, hwbits = wbits / 2 };

  using D = D<T>;
  using H = H<T>;

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
            add<S / 2>(r, {pp << hwbits});
          }
          else if constexpr(S % 2)
          {
            add<S / 2>(r, {pp << hwbits, pp >> hwbits});
          }
          else
          {
            add<S / 2>(r, {pp});
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
            add<S>(r, {T(pp)});
          }
          else
          {
            add<S>(r, {T(pp), T(pp >> wbits)});
          }
        }(),
        ...
      );
    }(std::make_index_sequence<N>());
  }
}

template <bool Rem = false, std::unsigned_integral T, std::size_t N>
constexpr void naidiv(T (&a)[N], T const (&b)[N]) noexcept
{ // wbits per iteration
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T>, hwbits = wbits / 2 };
  enum : T { dmax = (T(1) << hwbits) - 1 };

  T A[M];

  auto const CB(clz(b));

  if (auto const CA(clz(a)); CB >= CA) [[likely]]
  {
    copy(A, a);
    clear(a);
    lshl(A, CB);

    T B[M];
    rcopy<M - 1>(B, b);
    lshl(B, CB);

    H<T> const B0(B[M - 1] >> hwbits);

    auto k(N + 1 + (CB - CA) / wbits);
    wshr(B, M - k);

    auto const correction_step([&](T d) noexcept
        {
          if (d >> hwbits) [[unlikely]] d = dmax;
          lshr<hwbits>(B);
          decltype(B) tmp{};
          hwmul(B, d, tmp);
          sub(A, tmp);

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
  }
  else 
  {
    if constexpr(Rem) return; else clear(a);
  }

  //
  if constexpr(Rem)
  {
    lshr(A, CB);
    copy(a, A);
  }
}

}

#endif // INTT_ARITH_NAIDIV_HPP
