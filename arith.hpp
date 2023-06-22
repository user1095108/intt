#ifndef INTT_ARITH_HPP
# define INTT_ARITH_HPP
# pragma once

#include <climits> // CHAR_BIT
#include <cstddef> // std::size_t
#include <cstdint> // std::uintmax_t
#include <algorithm> // std::max()
#include <array> // std::to_array()
#include <bit> // std::countl_zero
#include <concepts> // std::floating_point, std::integral
#include <type_traits> // std::make_unsigned()
#include <utility> // std::index_sequence

namespace ar
{ // provides ops on arrays of unsigned ints

template <typename U>
static constexpr std::size_t bit_size_v(CHAR_BIT * sizeof(U));

template <auto C> static constexpr auto coeff() noexcept { return C; }

template <typename T>
using D = std::conditional_t<
  std::is_same_v<T, std::uint8_t>,
  std::uint16_t,
  std::conditional_t<
    std::is_same_v<T, std::uint16_t>,
    std::uint32_t,
    std::conditional_t<
      std::is_same_v<T, std::uint32_t>,
      std::uint64_t,
      void
    >
  >
>;

template <typename T>
using H = std::conditional_t<
  std::is_same_v<T, std::uint64_t>,
  std::uint32_t,
  std::conditional_t<
    std::is_same_v<T, std::uint32_t>,
    std::uint16_t,
    std::uint8_t
  >
>;

template <typename T, std::size_t N> using array_t = std::array<T, N>;

//
template <std::unsigned_integral T, std::size_t N>
constexpr bool any(array_t<T, N> const& a) noexcept
{ // a != 0
  return [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return (a[I] || ...);
    }(std::make_index_sequence<N>());
}

template <std::unsigned_integral T, std::size_t N>
constexpr void clear(array_t<T, N>& a) noexcept
{ // a = 0
  std::fill_n(a.data(), N, T{});
}

template <std::unsigned_integral T, std::size_t N>
constexpr bool eq(array_t<T, N> const& a, array_t<T, N> const& b) noexcept
{ // a == b
  return [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return ((a[I] == b[I]) && ...);
    }(std::make_index_sequence<N>());
}

template <std::unsigned_integral T, std::size_t N>
constexpr bool is_neg(array_t<T, N> const& a) noexcept
{ // a < 0
  using S = std::make_signed_t<T>;
  return S(a[N - 1]) < S{};
}

constexpr bool is_neg(std::integral auto const a) noexcept
{ // a < 0
  return a < decltype(a){};
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto ucmp(array_t<T, N> const& a, array_t<T, N> const& b) noexcept
{ // a <=> b
  auto r(a[N - 1] <=> b[N - 1]);

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (void)((r == 0) && ... && ((r = a[N - I - 2] <=> b[N - I - 2]) == 0));
  }(std::make_index_sequence<N - 1>());

  return r;
}

//
constexpr std::size_t clz(std::signed_integral auto const a) noexcept
{
  return std::countl_zero(std::make_unsigned_t<decltype(a)>(a));
}

constexpr std::size_t clz(std::unsigned_integral auto const a) noexcept
{
  return std::countl_zero(a);
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto clz(array_t<T, N> const& a) noexcept
{
  return [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      decltype(N) r{};

      enum : decltype(r) { wbits = bit_size_v<T> };

      (
        [&]() noexcept
        {
          decltype(r) const c(std::countl_zero(a[N - I - 1]));

          r += c;

          return wbits == c;
        }() && ...
      );

      return r;
    }(std::make_index_sequence<N>());
}

template <std::size_t D = 0, std::unsigned_integral T, std::size_t N0,
  std::size_t N1> requires (D < N0)
constexpr void copy(array_t<T, N0>& d, array_t<T, N1> const& s) noexcept
{ // d = s
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  { // set every element of d
    ((d[I] = {}), ...);
  }(std::make_index_sequence<D>());

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  { // set every element of d
    ((d[D + I] = I < N1 ? s[I] : T{}), ...);
  }(std::make_index_sequence<N0 - D>());
}

template <std::size_t D, std::unsigned_integral T, std::size_t N0,
  std::size_t N1> requires (D < N0)
constexpr void rcopy(array_t<T, N0>& d, array_t<T, N1> const& s) noexcept
{ // d = s
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  { // set every element of d
    ((d[N0 - I - 1] = {}), ...);
  }(std::make_index_sequence<N0 - D - 1>());

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  { // set every element of d
    ((d[D - I] = I < N1 ? s[N1 - I - 1] : T{}), ...);
  }(std::make_index_sequence<D + 1>());
}

//
template <std::size_t M, std::unsigned_integral T, std::size_t N>
  requires(bool(M) && (M < bit_size_v<T>))
constexpr auto& lshl(array_t<T, N>& a) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (
        a[N - 1 - I] = (a[N - 1 - I] << M) |
          (a[N - 1 - I - 1] >> (wbits - M))
      ),
      ...
    );
  }(std::make_index_sequence<N - 1>());

  a.front() <<= M;

  return a;
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto& lshl(array_t<T, N>& a, std::size_t M) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  if (M)
  {
    auto const shl([&]<auto ...I>(auto const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            a[N - 1 - I] = (a[N - 1 - I] << e) |
              (a[N - 1 - I - 1] >> (wbits - e))
          ),
          ...
        );

        a.front() <<= e;
      }
    );

    for (; M >= wbits; M -= wbits - 1)
    {
      shl(wbits - 1, std::make_index_sequence<N - 1>());
    }

    shl(M, std::make_index_sequence<N - 1>());
  }

  return a;
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto& ashr(array_t<T, N>& a, std::size_t M) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  if (M)
  {
    auto const shr([neg(is_neg(a)), &a]<auto ...I>(auto const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            a[I] = (a[I] >> e) | (a[I + 1] << (wbits - e))
          ),
          ...
        );

        a[N - 1] = (a[N - 1] >> e) | (neg ? ~T{} << (wbits - e) : T{});
      }
    );

    for (; M >= wbits; M -= wbits - 1)
    {
      shr(wbits - 1, std::make_index_sequence<N - 1>());
    }

    shr(M, std::make_index_sequence<N - 1>());
  }

  return a;
}

template <std::size_t M, std::unsigned_integral T, std::size_t N>
  requires(bool(M) && (M < bit_size_v<T>))
constexpr auto& lshr(array_t<T, N>& a) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (
        a[I] = (a[I + 1] << (wbits - M)) | (a[I] >> M)
      ),
      ...
    );
  }(std::make_index_sequence<N - 1>());

  a[N - 1] >>= M;

  return a;
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto& lshr(array_t<T, N>& a, std::size_t M) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  if (M)
  {
    auto const shr([&]<auto ...I>(auto const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            a[I] = (a[I + 1] << (wbits - e)) | (a[I] >> e)
          ),
          ...
        );

        a[N - 1] >>= e;
      }
    );

    for (; M >= wbits; M -= wbits - 1)
    {
      shr(wbits - 1, std::make_index_sequence<N - 1>());
    }

    shr(M, std::make_index_sequence<N - 1>());
  }

  return a;
}

template <std::size_t M, std::unsigned_integral T, std::size_t N>
constexpr auto& wshl(array_t<T, N>& a) noexcept requires(bool(M))
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (a[N - 1 - I] = M + I < N ? a[N - 1 - M - I] : T{}),
      ...
    );
  }(std::make_index_sequence<N>());

  return a;
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto& wshl(array_t<T, N>& a, std::size_t const M) noexcept
{
  std::size_t i{};

  for (auto const J(N - M); i != J; ++i) a[i + M] = a[i];
  for (; i != N;) a[N - i++] = {};

  return a;
}

template <std::size_t M, std::unsigned_integral T, std::size_t N>
constexpr auto& wshr(array_t<T, N>& a) noexcept requires(bool(M))
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (a[I] = M + I < N ? a[I + M] : T{}),
      ...
    );
  }(std::make_index_sequence<N>());

  return a;
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto& wshr(array_t<T, N>& a, std::size_t const M) noexcept
{
  std::size_t i{};

  for (auto const J(N - M); i != J; ++i) a[i] = a[i + M];
  for (; i != N;) a[i++] = {};

  return a;
}

template <std::unsigned_integral T, std::size_t N>
constexpr void set_bit(array_t<T, N>& a, std::size_t const i) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };
  a[i / wbits] |= T{1} << i % wbits;
}

template <std::size_t I, std::unsigned_integral T, std::size_t N>
constexpr bool test_bit(array_t<T, N> const& a) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };
  return a[I / wbits] & T{1} << I % wbits;
}

//
template <std::unsigned_integral T, std::size_t N>
constexpr auto& neg(array_t<T, N>& a) noexcept
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    bool c{true};

    ((c = (a[I] = T(~a[I]) + c) < c), ...);
  }(std::make_index_sequence<N>());

  return a;
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto& not_(array_t<T, N>& a) noexcept
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((a[I] = T(~a[I])), ...);
  }(std::make_index_sequence<N>());

  return a;
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto& and_(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((a[I] &= b[I]), ...);
  }(std::make_index_sequence<N>());

  return a;
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto& or_(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((a[I] |= b[I]), ...);
  }(std::make_index_sequence<N>());

  return a;
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto& xor_(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((a[I] ^= b[I]), ...);
  }(std::make_index_sequence<N>());

  return a;
}

//
template <std::size_t S = 0, std::unsigned_integral T,
  std::size_t N0, std::size_t N1>
constexpr auto& add(array_t<T, N0>& a, array_t<T, N1> const& b) noexcept
  requires(S < N0)
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    bool c;

    (
      [&]() noexcept
      {
        auto& s(a[S + I]);
        auto const a(s);

        if constexpr(!I)
        {
          c = (s += b.front()) < a;
        }
        else if constexpr(I < N1)
        {
          s += c + b[I];
          c = c ? s <= a : s < a;
        }
        else
        {
          c = (s += c) < c;
        }
      }(),
      ...
    );
  }(std::make_index_sequence<N0 - S>());

  return a;
}

template <std::unsigned_integral T, std::size_t N0, std::size_t N1>
constexpr auto& add(array_t<T, N0>& a, array_t<T, N1> const& b,
  std::size_t i) noexcept
{
  bool c;

  {
    auto const b0(b.front());

    c = (a[i++] += b0) < b0;
  }

  for (std::size_t j(1); (N1 != j) && (N0 != i);)
  {
    auto& s(a[i++]);
    auto const a(s);

    s += c + b[j++];
    c = c ? s <= a : s < a;
  }

  while (N0 != i) c = (a[i++] += c) < c;

  return a;
}

template <std::size_t S = 0, std::unsigned_integral T,
  std::size_t N0, std::size_t N1>
constexpr auto& sub(array_t<T, N0>& a, array_t<T, N1> const& b) noexcept
  requires(S < N0)
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    bool c;

    (
      [&]() noexcept
      {
        auto& d(a[S + I]);
        auto const a(d);

        if constexpr(!I)
        {
          c = (d -= b.front()) > a;
        }
        else if constexpr(I < N1)
        {
          d = d - b[I] - c;
          c = c ? d >= a : d > a;
        }
        else
        {
          c = (d -= c) > a;
        }
      }(),
      ...
    );
  }(std::make_index_sequence<N0 - S>());

  return a;
}

template <bool Rem, auto F, std::unsigned_integral T, std::size_t N>
constexpr void sdiv(array_t<T, N>& a, array_t<T, N> const& b) noexcept
{
  auto const s(Rem ? is_neg(a) : is_neg(a) != is_neg(b));

  if (is_neg(a)) neg(a);

  array_t<T, N> B;

  F(a, is_neg(b) ? copy(B, b), neg(B), B : b);

  if (s) neg(a);
}

}

#endif // INTT_ARITH_HPP
