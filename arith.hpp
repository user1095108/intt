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
template <typename T>
constexpr auto size() noexcept
{
  return sizeof(T) / sizeof(std::declval<T>()[0]);
}

constexpr bool any(auto const& a) noexcept
{ // a != 0
  constexpr auto N{size<decltype(a)>()};

  return [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return (a[I] || ...);
    }(std::make_index_sequence<N>());
}

constexpr void clear(auto& a) noexcept
{ // a = 0
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

  std::fill_n(std::begin(a), N, T{});
}

constexpr bool eq(auto const& a, decltype(a) b) noexcept
{ // a == b
  constexpr auto N{size<decltype(a)>()};

  return [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return ((a[I] == b[I]) && ...);
    }(std::make_index_sequence<N>());
}

constexpr bool is_neg(auto const& a) noexcept
{ // a < 0
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

  using S = std::make_signed_t<T>;
  return S(a[N - 1]) < S{};
}

constexpr bool is_neg(std::integral auto const a) noexcept
{ // a < 0
  return a < decltype(a){};
}

constexpr auto ucmp(auto const& a, decltype(a) b) noexcept
{ // a <=> b
  constexpr auto N{size<decltype(a)>()};

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

constexpr auto clz(auto const& a) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

  return [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      std::size_t r{};

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

template <std::size_t D = 0>
constexpr auto&& copy(auto&& d, auto const& s) noexcept
  requires(D < size<decltype(d)>())
{ // d = s
  using T = std::remove_cvref_t<decltype(d[0])>;
  constexpr auto N0{size<decltype(d)>()};
  constexpr auto N1{size<decltype(s)>()};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  { // set every element of d
    ((d[I] = {}), ...);
  }(std::make_index_sequence<D>());

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  { // set every element of d
    ((d[D + I] = I < N1 ? s[I] : T{}), ...);
  }(std::make_index_sequence<N0 - D>());

  return d;
}

template <std::size_t D>
constexpr auto&& rcopy(auto&& d, auto const& s) noexcept
  requires(D < size<decltype(d)>())
{ // d = s
  using T = std::remove_cvref_t<decltype(d[0])>;
  constexpr auto N0{size<decltype(d)>()};
  constexpr auto N1{size<decltype(s)>()};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  { // set every element of d
    ((d[N0 - I - 1] = {}), ...);
  }(std::make_index_sequence<N0 - D - 1>());

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  { // set every element of d
    ((d[D - I] = I < N1 ? s[N1 - I - 1] : T{}), ...);
  }(std::make_index_sequence<D + 1>());

  return d;
}

//
template <std::size_t M>
constexpr auto&& lshl(auto&& a) noexcept
  requires(bool(M) && (M < bit_size_v<std::remove_cvref_t<decltype(a[0])>>))
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

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

constexpr auto&& lshl(auto&& a, std::size_t M) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

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

constexpr auto&& ashr(auto&& a, std::size_t M) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

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

template <std::size_t M>
constexpr auto&& lshr(auto&& a) noexcept
  requires(bool(M) && (M < bit_size_v<std::remove_cvref_t<decltype(a[0])>>))
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

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

constexpr auto&& lshr(auto&& a, std::size_t M) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

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

template <std::size_t M> requires(bool(M))
constexpr auto&& wshl(auto&& a) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (a[N - 1 - I] = M + I < N ? a[N - 1 - M - I] : T{}),
      ...
    );
  }(std::make_index_sequence<N>());

  return a;
}

constexpr auto&& wshl(auto&& a, std::size_t const M) noexcept
{
  constexpr auto N{size<decltype(a)>()};

  std::size_t i{};

  for (auto const J(N - M); i != J; ++i) a[i + M] = a[i];
  for (; i != N;) a[N - i++] = {};

  return a;
}

template <std::size_t M> requires(bool(M))
constexpr auto&& wshr(auto&& a) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  constexpr auto N{size<decltype(a)>()};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (a[I] = M + I < N ? a[I + M] : T{}),
      ...
    );
  }(std::make_index_sequence<N>());

  return a;
}

constexpr auto&& wshr(auto&& a, std::size_t const M) noexcept
{
  constexpr auto N{size<decltype(a)>()};

  std::size_t i{};

  for (auto const J(N - M); i != J; ++i) a[i] = a[i + M];
  for (; i != N;) a[i++] = {};

  return a;
}

constexpr void set_bit(auto& a, std::size_t const i) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { wbits = bit_size_v<T> };
  a[i / wbits] |= T{1} << i % wbits;
}

template <std::size_t I>
constexpr bool test_bit(auto const& a) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { wbits = bit_size_v<T> };
  return a[I / wbits] & T{1} << I % wbits;
}

//
constexpr auto&& neg(auto&& a) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    bool c{true};

    ((c = (a[I] = T(~a[I]) + c) < c), ...);
  }(std::make_index_sequence<size<decltype(a)>()>());

  return a;
}

constexpr auto&& not_(auto&& a) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((a[I] = T(~a[I])), ...);
  }(std::make_index_sequence<size<decltype(a)>()>());

  return a;
}

constexpr auto&& and_(auto&& a, auto const& b) noexcept
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((a[I] &= b[I]), ...);
  }(std::make_index_sequence<size<decltype(a)>()>());

  return a;
}

constexpr auto&& or_(auto&& a, auto const& b) noexcept
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((a[I] |= b[I]), ...);
  }(std::make_index_sequence<size<decltype(a)>()>());

  return a;
}

constexpr auto&& xor_(auto&& a, auto const& b) noexcept
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((a[I] ^= b[I]), ...);
  }(std::make_index_sequence<size<decltype(a)>()>());

  return a;
}

//
template <std::size_t S = 0>
constexpr auto&& add(auto&& a, auto const& b) noexcept
  requires(S < size<decltype(a)>())
{
  constexpr auto N0{size<decltype(a)>()};
  constexpr auto N1{size<decltype(b)>()};

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

constexpr auto&& add(auto&& a, auto const& b, std::size_t i) noexcept
{
  constexpr auto N0{size<decltype(a)>()};
  constexpr auto N1{size<decltype(b)>()};

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

template <std::size_t S = 0>
constexpr auto&& sub(auto&& a, auto const& b) noexcept
  requires(S < size<decltype(a)>())
{
  constexpr auto N0{size<decltype(a)>()};
  constexpr auto N1{size<decltype(b)>()};

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

template <bool Rem, auto F>
constexpr auto&& sdiv(auto&& a, auto const& b) noexcept
{
  auto const s(Rem ? is_neg(a) : is_neg(a) != is_neg(b));

  if (is_neg(a)) neg(a);

  std::remove_cvref_t<decltype(a)> B;

  F(a, is_neg(b) ? copy(B, b), neg(B), B : b);

  if (s) neg(a);

  return a;
}

}

#endif // INTT_ARITH_HPP
