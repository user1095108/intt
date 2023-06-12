#ifndef INTT_ARITH_NEWDIV_HPP
# define INTT_ARITH_NEWDIV_HPP
# pragma once

#include "naimul.hpp"

namespace ar
{ // provides Newton-Raphson method implementations of div

template <std::size_t O, std::unsigned_integral T, std::size_t N>
constexpr void newmul(T (&a)[N], T const (&b)[N]) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  using D = D<T>;
  using H = H<T>;

  auto const nega(is_neg(a)), negb(is_neg(b));

  T r[N]{};

  if constexpr(std::is_same_v<T, std::uintmax_t>)
  {
    enum : std::size_t { M = 2 * O, hwbits = wbits / 2 };

    for (std::size_t i{}; M != i; ++i)
    {
      for (std::size_t j{}; M != j; ++j)
      {
        T const pp(T(H(a[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0))) *
          H(b[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0)));

        auto const S(i + j);

        S % 2 ?
          add(r, {pp << hwbits, pp >> hwbits}, S / 2) :
          add(r, {pp}, S / 2);
      }
    }
  }
  else
  {
    for (std::size_t i{}; O != i; ++i)
    {
      for (std::size_t j{}; O != j; ++j)
      {
        D const pp(D(a[i]) * b[j]);

        add(r, {T(pp), T(pp >> wbits)}, i + j);
      }
    }
  }

  //
  wshr<O>(r);

  r[O] = a[O] * b[O];

  if (nega != negb)
  {
    for (auto i{O + 1}; N != i; r[i++] = ~T{});
  }

  if (a[O])
  {
    if (T bb[O]; copy(bb, b), nega)
    {
      auto A{-a[O]};
      do sub(r, bb); while (--A);
    }
    else
    {
      auto A{a[O]};
      do add(r, bb); while (--A);
    }
  }

  if (b[O])
  {
    if (T aa[O]; copy(aa, a), negb)
    {
      auto B{-b[O]};
      do sub(r, aa); while (--B);
    }
    else
    {
      auto B{b[O]};
      do add(r, aa); while (--B);
    }
  }

  //
  copy(a, r);
}

//
template <typename T, std::size_t M>
static constexpr auto gldend{
  []<auto ...I>(std::index_sequence<I...>) noexcept
  {
    T A[M]{};
    not_(A);
    wshr<M / 2>(A);

    return std::array<T, M>{A[I]...};
  }(std::make_index_sequence<M>())
};

template <typename T, std::size_t M, unsigned A0, unsigned B0>
static constexpr auto newc{
  []<auto ...I>(std::index_sequence<I...>) noexcept
  {
    T A[M]{T(A0)};
    wshl<M / 2>(A);
    T const B[M]{T(B0)};
    naidiv(A, B);

    return std::array<T, M>{A[I]...};
  }(std::make_index_sequence<M>())
};

//
template <bool Rem = false, typename T, std::size_t N>
constexpr auto glddiv(T (&a)[N], T const (&b)[N]) noexcept
{
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T>, bits = N * wbits };

  T q[N];

  {
    T A[M];
    copy(A, a);

    T B[M];
    copy(B, b);
    auto const C(clz(b));
    lshl(B, C);

    while (!eq(gldend<T, M>, B))
    {
      T k[M];
      copy(k, newc<T, M, 2, 1>);
      sub(k, B);

      newmul<N>(B, k);
      newmul<N>(A, k);
    }

    //
    lshr(A, bits - C);

    //
    copy(q, A);
    naimul(q, b);
    sub(a, q); // a = a - q * b

    //
    copy(q, A);
  }

  if constexpr(Rem)
  {
    if (ucmp(a, b) >= 0) sub(a, b);
  }
  else
  {
    if (ucmp(a, b) >= 0) add(q, {T(1)});

    copy(a, q);
  }
}

template <bool Rem = false, typename T, std::size_t N>
constexpr auto newdiv(T (&a)[N], T const (&b)[N]) noexcept
{
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T>, bits = N * wbits };

  T q[N];

  {
    T B[M];
    copy(B, b);
    auto const C(clz(b));
    lshl(B, C);

    // xn = 2 - b
    // xn = 48/17 - 32/17 * b

    T xn[M];
    copy(xn, newc<T, M, 48, 17>);

    T tmp[M];
    copy(tmp, newc<T, M, 32, 17>);
    newmul<N>(tmp, B);

    sub(xn, tmp);

    // xn = xn(2 - a * xn)
    for (; copy(tmp, B), newmul<N>(tmp, xn), tmp[N - 1];)
    {
      T k[M];
      copy(k, newc<T, M, 2, 1>);

      // xn = newmul<N>(xn, k - tmp);
      sub(k, tmp);
      newmul<N>(xn, k);
    }

    copy(B, a);
    newmul<N>(B, xn); // a * inv(b)
    lshr(B, bits - C);
    copy(q, B);
  }

  //
  if constexpr(Rem)
  {
    T r[N];
    copy(r, q);
    naimul(r, b);
    sub(a, r); // r = a - q * b
  }
  else
  {
    copy(a, q);
  }
}

}

#endif // INTT_ARITH_NEWDIV_HPP
