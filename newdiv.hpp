#ifndef INTT_ARITH_NEWDIV_HPP
# define INTT_ARITH_NEWDIV_HPP
# pragma once

#include "naimul.hpp"

namespace ar
{ // provides Newton-Raphson method implementations of div

template <std::size_t O, std::unsigned_integral T, std::size_t N>
constexpr auto& newmul(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  using D = D<T>;
  using H = H<T>;

  array_t<T, N> r{};

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
          add(r, array_t<T, 2>{pp << hwbits, pp >> hwbits}, S / 2) :
          add(r, array_t<T, 1>{pp}, S / 2);
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

        add(r, array_t<T, 2>{T(pp), T(pp >> wbits)}, i + j);
      }
    }
  }

  //
  wshr<O>(r);

  r[O] = a[O] * b[O];

  auto const nega(is_neg(a)), negb(is_neg(b));

  if (nega != negb)
  {
    for (auto i{O + 1}; N != i; r[i++] = ~T{});
  }

  if (a[O])
  {
    if (array_t<T, O> bb; copy(bb, b), nega)
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
    if (array_t<T, O> aa; copy(aa, a), negb)
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

  return a;
}

//
template <typename T, std::size_t M>
static constexpr auto gldend{[]() noexcept
  {
    array_t<T, M> A{};
    not_(A);
    wshr<M / 2>(A);

    return A;
  }()
};

template <typename T, std::size_t M, unsigned A0, unsigned B0>
static constexpr auto newc{[]() noexcept
  {
    array_t<T, M> A{T(A0)};
    wshl<M / 2>(A);
    array_t<T, M> const B{T(B0)};
    naidiv(A, B);

    return A;
  }()
};

//
template <bool Rem = false, typename T, std::size_t N>
constexpr auto glddiv(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T>, bits = N * wbits };

  array_t<T, N> q;

  {
    array_t<T, M> A;
    copy(A, a);

    array_t<T, M> B;
    copy(B, b);
    auto const C(clz(b));
    lshl(B, C);

    while (!eq(gldend<T, M>, B))
    {
      auto k{newc<T, M, 2, 1>};
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
    if (ucmp(a, b) >= 0) add(q, array_t<T, 1>{T(1)});

    copy(a, q);
  }
}

template <bool Rem = false, typename T, std::size_t N>
constexpr auto newdiv(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{
  enum : std::size_t { M = 2 * N, wbits = bit_size_v<T>, bits = N * wbits };

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

    sub(xn, newmul<N>(tmp, B));

    // xn = xn(2 - a * xn)
    for (; copy(tmp, B), newmul<N>(tmp, xn), tmp[N - 1];)
    {
      // xn = newmul<N>(xn, k - tmp);
      auto k{newc<T, M, 2, 1>};
      newmul<N>(xn, sub(k, tmp));
    }

    copy(B, a);
    lshr(newmul<N>(B, xn), bits - C); // a * inv(b)
    copy(q, B);
  }

  //
  if constexpr(Rem)
  {
    naimul(q, b);
    sub(a, q); // a = r = a - q * b
  }
  else
  {
    copy(a, q);
  }
}

}

#endif // INTT_ARITH_NEWDIV_HPP
