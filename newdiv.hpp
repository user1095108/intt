#ifndef INTT_ARITH_NEWDIV_HPP
# define INTT_ARITH_NEWDIV_HPP
# pragma once

#include "naimul.hpp"

namespace ar
{ // provides Newton-Raphson method implementations of div

template <std::size_t N>
constexpr auto&& newmul(uarray_c auto&& a, uarray_c auto const& b) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { M = size<decltype(a)>(), wbits = bit_size_v<T> };
  enum : std::size_t { hwbits = wbits / 2 };

  array_t<T, M> r{};

  if constexpr(std::is_same_v<T, std::uintmax_t>)
  {
    for (std::size_t i{}; M != i; ++i)
    {
      for (std::size_t j{}; M != j; ++j)
      {
        T const pp(T(H<T>(a[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0))) *
          H<T>(b[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0)));

        auto const S(i + j);

        S % 2 ?
          add(r, array_t<T, 2>{pp << hwbits, pp >> hwbits}, S / 2) :
          add(r, array_t<T, 1>{pp}, S / 2);
      }
    }
  }
  else
  {
    for (std::size_t i{}; N != i; ++i)
    {
      for (std::size_t j{}; N != j; ++j)
      {
        D<T> const pp(D<T>(a[i]) * b[j]);

        add(r, array_t<T, 2>{T(pp), T(pp >> wbits)}, i + j);
      }
    }
  }

  //
  wshr<N>(r);

  auto const nega(is_neg(a)), negb(is_neg(b));

  if (nega != negb)
  {
    //for (auto i{N + 1}; M != i; r[i++] = ~T{});
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      ((r[N + 1 + I] = ~T{}), ...);
    }(std::make_index_sequence<N - 1>());

    add(r, array_t<T, 1>{T(1)});
  }

  r[N] = a[N] * b[N];

  if (auto A(a[N]); A)
  {
    if (nega)
    {
      do sub<0, N>(r, b); while (++A);
    }
    else
    {
      do add<0, N>(r, b); while (--A);
    }
  }

  if (auto B(b[N]); B)
  {
    if (negb)
    {
      do sub<0, N>(r, a); while (++B);
    }
    else
    {
      do add<0, N>(r, a); while (--B);
    }
  }

  //
  return copy(a, r);
}

template <std::size_t N>
constexpr auto&& newmul2(uarray_c auto&& a, uarray_c auto const& b) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { M = size<decltype(a)>(), wbits = bit_size_v<T> };
  enum : std::size_t { hwbits = wbits / 2 };

  array_t<T, M> r{};

  if constexpr(std::is_same_v<T, std::uintmax_t>)
  {
    for (std::size_t i{}; M != i; ++i)
    {
      for (std::size_t j{}; M != j; ++j)
      {
        T const pp(T(H<T>(a[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0))) *
          H<T>(b[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0)));

        auto const S(i + j);

        S % 2 ?
          add(r, array_t<T, 2>{pp << hwbits, pp >> hwbits}, S / 2) :
          add(r, array_t<T, 1>{pp}, S / 2);
      }
    }
  }
  else
  {
    for (std::size_t i{}; N != i; ++i)
    {
      for (std::size_t j{}; N != j; ++j)
      {
        D<T> const pp(D<T>(a[i]) * b[j]);

        add(r, array_t<T, 2>{T(pp), T(pp >> wbits)}, i + j);
      }
    }
  }

  //
  wshr<N>(r);

  r[N] = a[N] * b[N];

  if (auto A(a[N]); A) do add<0, N>(r, b); while (--A);
  if (auto B(b[N]); B) do add<0, N>(r, a); while (--B);

  //
  return copy(a, r);
}

//
template <typename T, std::size_t M>
static constexpr auto gldend{wshr<M / 2>(not_(array_t<T, M>{}))};

template <typename T, std::size_t M, unsigned A0, unsigned B0>
static constexpr auto newc{
  naidiv(wshl<M / 2>(array_t<T, M>{T(A0)}), array_t<T, M>{T(B0)})
};

//
template <bool Rem = false>
constexpr auto&& glddiv(uarray_c auto&& a, uarray_c auto const& b) noexcept
  requires(
    (size<decltype(a)>() == size<decltype(b)>()) &&
    std::is_same_v<
      std::remove_cvref_t<decltype(a[0])>,
      std::remove_cvref_t<decltype(b[0])>
    >
  )
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { N = size<decltype(a)>(), M = 2 * N };
  enum : std::size_t { wbits = bit_size_v<T>, bits = N * wbits };

  array_t<T, M> A;

  {
    copy(A, a);

    array_t<T, M> B;
    auto const C(clz(b));
    lshl(copy(B, b), C);

    while (!eq<N, 0>(gldend<T, M>, B))
    {
      auto k{newc<T, M, 2, 1>};
      sub(k, B);

      newmul2<N>(B, k);
      newmul2<N>(A, k);
    }

    //
    array_t<T, N> q;
    sub(a, naimul(copy(q, lshr(A, bits - C)), b)); // a = a - q * b
  }

  //
  if constexpr(auto const c(ucmp(a, b) >= 0); Rem)
  {
    return c ? sub(a, b) : a;
  }
  else
  {
    copy(a, A);
    return c ? add(a, array_t<T, 1>{T(1)}) : a;
  }
}

template <bool Rem = false>
constexpr auto&& newdiv(uarray_c auto&& a, uarray_c auto const& b) noexcept
  requires(
    (size<decltype(a)>() == size<decltype(b)>()) &&
    std::is_same_v<
      std::remove_cvref_t<decltype(a[0])>,
      std::remove_cvref_t<decltype(b[0])>
    >
  )
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { N = size<decltype(a)>(), M = 2 * N };
  enum : std::size_t { wbits = bit_size_v<T>, bits = N * wbits };

  array_t<T, N> q;

  {
    array_t<T, M> B;
    copy(B, b);
    auto const C(clz(b));
    lshl(B, C);

    // xn = 2 - b
    // xn = 48/17 - 32/17 * b

    auto xn{newc<T, M, 48, 17>};
    auto tmp{newc<T, M, 32, 17>};

    sub(xn, newmul2<N>(tmp, B));

    // xn = xn(2 - a * xn)
    for (; newmul2<N>(copy(tmp, B), xn), !eq<N, 0>(tmp, newc<T, M, 1, 1>);)
    {
      // xn = newmul<N>(xn, k - tmp);
      newmul2<N>(xn, neg(sub(tmp, newc<T, M, 2, 1>)));
    }

    //
    copy(q, lshr(newmul2<N>(copy(B, a), xn), bits - C)); // a * inv(b)
  }

  //
  return Rem ? sub(a, naimul(q, b)) : copy(a, q); // a = r = a - q * b
}

}

#endif // INTT_ARITH_NEWDIV_HPP
