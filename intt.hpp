#ifndef LONGINT_HPP
# define LONGINT_HPP
# pragma once

#include <cassert>
#include <climits>

#include <array>

#include <limits>

#include <ostream>

#include <sstream>

#include <utility>

#include <type_traits>

namespace intt
{

namespace detail
{

constexpr auto hash_combine(auto&& ...v) noexcept requires(bool(sizeof...(v)))
{
  std::size_t seed{672807365};

  return (
    (
      seed ^= std::hash<std::remove_cvref_t<decltype(v)>>()(
        std::forward<decltype(v)>(v)) + 0x9e3779b9 + (seed << 6) +
        (seed >> 2)
    ),
    ...
  );
}

}

template <typename T, unsigned N>
class intt
{
static_assert(std::is_unsigned_v<T>);
static_assert(N > 0);

public:
  using value_type = std::array<T, N>;

  value_type v_{};

public:
  enum : unsigned { bits_e = sizeof(T) * CHAR_BIT };
  enum : unsigned { bits = N * bits_e };

  enum : T { max_e = std::numeric_limits<T>::max() };

  enum : unsigned { size = N };

  constexpr intt() noexcept = default;

  constexpr intt(decltype(v_) const& v) noexcept :
    v_(v)
  {
  }

  template <typename U> requires(std::is_integral_v<U>)
  constexpr intt(U const v) noexcept
  {
    [&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
    {
      if constexpr (std::is_signed_v<U>)
      {
        (
          (
            v_[I] = I * bits_e < sizeof(U) * CHAR_BIT ?
              v >> I * bits_e :
              v >= 0 ? T{} : ~T{}
          ),
          ...
        );
      }
      else
      {
        (
          (
            v_[I] = I * bits_e < sizeof(U) * CHAR_BIT ?
              v >> I * bits_e :
              (v >> ((sizeof(U) * CHAR_BIT) - 1 ? ~T{} : T{}))
          ),
          ...
        );
      }
    }(std::make_index_sequence<N>());
  }

  constexpr intt(intt const&) = default;
  constexpr intt(intt&&) = default;

  // assignment
  constexpr intt& operator=(intt const&) = default;
  constexpr intt& operator=(intt&&) = default;

  #define INTT_ASSIGNMENT(OP)\
    template <typename U>\
    constexpr auto& operator OP ## =(U&& a) noexcept\
    {\
      return *this = *this OP std::forward<U>(a);\
    }

  INTT_ASSIGNMENT(+)
  INTT_ASSIGNMENT(-)
  INTT_ASSIGNMENT(*)
  INTT_ASSIGNMENT(/)

  constexpr auto& operator<<=(unsigned i) noexcept
  {
    return *this = *this << i;
  }

  constexpr auto& operator>>=(unsigned i) noexcept
  {
    return *this = *this >> i;
  }

  //
  constexpr explicit operator bool() const noexcept
  {
    return [&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
      {
        return (v_[I] || ...);
      }(std::make_index_sequence<N>());
  }

  template <typename U>
    requires(std::is_integral_v<U> && std::is_signed_v<U>)
  constexpr explicit operator U() const noexcept
  {
    return [&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
      {
        if constexpr (bool(sizeof...(I)))
        {
          return (
            (U(v_[I]) << I * bits_e) |
            ...
          );
        }
        else
        {
          return v_[0];
        }
      }(std::make_index_sequence<(sizeof(U) * CHAR_BIT) / bits_e>());
  }

  // increment, decrement
  constexpr auto& operator++() noexcept { return *this += intt{1}; }
  constexpr auto& operator--() noexcept { return *this -= intt{1}; }

  constexpr auto operator++(int) const noexcept { return *this + intt{1}; }
  constexpr auto operator--(int) const noexcept { return *this - intt{1}; }

  // member access
  constexpr auto operator[](unsigned const i) const noexcept { return v_[i]; }

  //
  constexpr auto operator~() const noexcept
  {
    return ([&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
      {
        return intt{intt::value_type{T(~v_[I])...}};
      }
    )(std::make_index_sequence<N>());
  }

  constexpr auto operator+() const noexcept { return *this; }
  constexpr auto operator-() const noexcept { return ~*this + intt{1}; }

  //
  template <typename A, unsigned B>
  friend constexpr bool operator==(intt<A, B> const&,
    intt<A, B> const&) noexcept;

  template <typename A, unsigned B, typename C, unsigned D>
  friend constexpr auto operator+(intt<A, B> const&,
    intt<C, D> const&) noexcept;

  template <typename A, unsigned B, typename C, unsigned D>
  friend constexpr auto operator-(intt<A, B> const&,
    intt<C, D> const&) noexcept;

  template <typename A, unsigned B>
  friend constexpr auto operator<<(intt<A, B> const&, unsigned) noexcept;
  template <typename A, unsigned B>
  friend constexpr auto operator>>(intt<A, B> const&, unsigned) noexcept;
};

//arithmetic//////////////////////////////////////////////////////////////////

template <typename T, unsigned N>
constexpr auto operator+(intt<T, N> const& a,
  intt<T, N> const& b) noexcept
{
  using r_t = intt<T, N>;

  return ([&]<std::size_t ...I>(
    std::index_sequence<I...>) noexcept
    {
      intt<T, N> r;

      bool carry{};

      (
        (
          r.v_[I] = a[I] + b[I] + carry,
          carry = a[I] > r_t::max_e - b[I] - carry
        ),
        ...
      );

      return r;
    }
  )(std::make_index_sequence<N>());
}

template <typename T, unsigned N>
constexpr auto operator-(intt<T, N> const& a,
  intt<T, N> const& b) noexcept
{
  return a + (-b);
}

template <typename T, unsigned N>
constexpr auto operator*(intt<T, N> const& a,
  intt<T, N> const& b) noexcept
{
  using r_t = intt<T, N>;

  return [&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
    {
      return (
        [&]<auto J>() noexcept
        {
          return (
            (
              r_t(a[J] * b[I]) << (J + I) * r_t::bits_e
            ) +
            ...
          );
        }.template operator()<I>() +
        ...
      );
    }(std::make_index_sequence<N>());
}

template <typename T, unsigned N>
constexpr auto operator/(intt<T, N> a, intt<T, N> b) noexcept
{
  using r_t = intt<T, N>;

  if (is_negative(b))
  {
    a = -a;
    b = -b;
  }

  r_t q;
  r_t r(a);

  std::cout << int(a) << " " << int(b) << " " << int(q) << " " << int(r) << " : " << to_raw(r) << std::endl;

  if (is_negative(a))
  {
    while (r >= b)
    {
      --q;
      r += b;
    }
  }
  else
  {
    while (r >= b)
    {
      ++q;
      r -= b;
    }
  }

  return q;
}

template <typename A, unsigned B>
constexpr auto operator%(intt<A, B> const& a,
  intt<A, B> const& b) noexcept
{
  return a - (a / b) * b;
}

// conversions
template <typename A, unsigned B, typename U>
constexpr auto operator+(intt<A, B> const& a, U const b) noexcept
{
  static_assert(std::is_arithmetic_v<U>);
  return a + intt<A, B>(b);
}

template <typename A, unsigned B, typename U>
constexpr auto operator-(intt<A, B> const& a, U const b) noexcept
{
  static_assert(std::is_arithmetic_v<U>);
  return a - intt<A, B>(b);
}

template <typename A, unsigned B, typename U>
constexpr auto operator*(intt<A, B> const& a, U const b) noexcept
{
  static_assert(std::is_arithmetic_v<U>);
  return a * intt<A, B>(b);
}

template <typename A, unsigned B, typename U>
constexpr auto operator/(intt<A, B> const& a, U const b) noexcept
{
  static_assert(std::is_arithmetic_v<U>);
  return a / intt<A, B>(b);
}

template <typename A, unsigned B, typename U>
constexpr auto operator%(intt<A, B> const& a, U const b) noexcept
{
  static_assert(std::is_arithmetic_v<U>);
  return a % intt<A, B>(b);
}

// conversions
template <typename A, unsigned B, typename U>
constexpr auto operator+(U const a, intt<A, B> const& b) noexcept
{
  static_assert(std::is_arithmetic_v<U>);
  return intt<A, B>(a) + b;
}

template <typename A, unsigned B, typename U>
constexpr auto operator-(U const a, intt<A, B> const& b) noexcept
{
  static_assert(std::is_arithmetic_v<U>);
  return intt<A, B>(a) - b;
}

template <typename A, unsigned B, typename U>
constexpr auto operator*(U const a, intt<A, B> const& b) noexcept
{
  static_assert(std::is_arithmetic_v<U>);
  return intt<A, B>(a) * b;
}

template <typename A, unsigned B, typename U>
constexpr auto operator/(U const a, intt<A, B> const& b) noexcept
{
  static_assert(std::is_arithmetic_v<U>);
  return intt<A, B>(a) / b;
}

template <typename A, unsigned B, typename U>
constexpr auto operator%(U const a, intt<A, B> const& b) noexcept
{
  static_assert(std::is_arithmetic_v<U>);
  return intt<A, B>(a) % b;
}

//
template <typename T, unsigned N>
constexpr auto operator<<(intt<T, N> const& a, unsigned M) noexcept
{
  using r_t = intt<T, N>;

  auto r(a);

  auto const shl([&]<std::size_t ...I>(unsigned const e,
    std::index_sequence<I...>) noexcept
    {
      (
        (
          r.v_[N - 1 - I] = 
            (r[N - 1 - I] << e) |
            (r[N - 1 - I - 1] >> (r_t::bits_e - e))
        ),
        ...
      );

      r.v_[0] <<= e;
    }
  );

  while (M >= r_t::bits_e)
  {
    shl.template operator()(r_t::bits_e, std::make_index_sequence<N - 1>());
    M -= r_t::bits_e;
  }

  shl.template operator()(M % r_t::bits_e, std::make_index_sequence<N - 1>());

  return r;
}

template <typename T, unsigned N>
constexpr auto operator>>(intt<T, N> const& a, unsigned M) noexcept
{
  using r_t = intt<T, N>;

  auto const neg(is_negative(a));

  auto r(a);

  auto const shr([&]<std::size_t ...I>(unsigned const e,
    std::index_sequence<I...>) noexcept
    {
      (
        (
          r.v_[I] =
            (r[I] >> e) |
            (r[I + 1] << (r_t::bits_e - e))
        ),
        ...
      );

      r.v_[N - 1] = (r.v_[N - 1] >> e) |
        (neg ? T(~T{}) << (r_t::bits_e - e) : T{});
    }
  );

  while (M >= r_t::bits_e)
  {
    shr.template operator()(r_t::bits_e, std::make_index_sequence<N - 1>());
    M -= r_t::bits_e;
  }

  shr.template operator()(M % r_t::bits_e, std::make_index_sequence<N - 1>());

  return r;
}

//comparison//////////////////////////////////////////////////////////////////
template <typename A, unsigned B>
constexpr bool operator==(intt<A, B> const& a,
  intt<A, B> const& b) noexcept
{
  return a.v_ == b.v_;
}

template <typename A, unsigned B>
constexpr auto operator!=(intt<A, B> const& a,
  intt<A, B> const& b) noexcept
{
  return !(a == b);
}

//
template <typename A, unsigned B>
constexpr bool operator<(intt<A, B> const& a,
  intt<A, B> const& b) noexcept
{
  return is_negative(a - b);
}

template <typename A, unsigned B>
constexpr auto operator>(intt<A, B> const& a,
  intt<A, B> const& b) noexcept
{
  return b < a;
}

template <typename A, unsigned B>
constexpr auto operator<=(intt<A, B> const& a,
  intt<A, B> const& b) noexcept
{
  return !(b < a);
}

template <typename A, unsigned B>
constexpr auto operator>=(intt<A, B> const& a,
  intt<A, B> const& b) noexcept
{
  return !(a < b);
}

#if __cplusplus > 201703L
template <typename A, unsigned B>
constexpr auto operator<=>(intt<A, B> const& a,
  intt<A, B> const& b) noexcept
{
  return (a > b) - (a < b);
}
#endif

// conversions
template <typename A, unsigned B, typename U>
constexpr auto operator==(intt<A, B> const& a, U const& b) noexcept
{
  return a == intt<A, B>(b);
}

template <typename A, unsigned B, typename U>
constexpr auto operator!=(intt<A, B> const& a, U const& b) noexcept
{
  return a != intt<A, B>(b);
}

template <typename A, unsigned B, typename U>
constexpr auto operator<(intt<A, B> const& a, U const& b) noexcept
{
  return a < intt<A, B>(b);
}

template <typename A, unsigned B, typename U>
constexpr auto operator>(intt<A, B> const& a, U const& b) noexcept
{
  return a > intt<A, B>(b);
}

template <typename A, unsigned B, typename U>
constexpr auto operator<=(intt<A, B> const& a, U const& b) noexcept
{
  return a <= intt<A, B>(b);
}

template <typename A, unsigned B, typename U>
constexpr auto operator>=(intt<A, B> const& a, U const& b) noexcept
{
  return a >= intt<A, B>(b);
}

#if __cplusplus > 201703L
template <typename A, unsigned B, typename U>
constexpr auto operator<=>(intt<A, B> const& a, U const& b) noexcept
{
  return (a > b) - (a < b);
}
#endif

// conversions
template <typename A, unsigned B, typename U>
constexpr auto operator==(U const& a, intt<A, B> const& b) noexcept
{
  return intt<A, B>(a) == b;
}

template <typename A, unsigned B, typename U>
constexpr auto operator!=(U const& a, intt<A, B> const& b) noexcept
{
  return intt<A, B>(a) != b;
}

template <typename A, unsigned B, typename U>
constexpr auto operator<(U const& a, intt<A, B> const& b) noexcept
{
  return intt<A, B>(a) < b;
}

template <typename A, unsigned B, typename U>
constexpr auto operator>(U const& a, intt<A, B> const& b) noexcept
{
  return intt<A, B>(a) > b;
}

template <typename A, unsigned B, typename U>
constexpr auto operator<=(U const& a, intt<A, B> const& b) noexcept
{
  return intt<A, B>(a) <= b;
}

template <typename A, unsigned B, typename U>
constexpr auto operator>=(U const& a, intt<A, B> const& b) noexcept
{
  return intt<A, B>(a) >= b;
}

//misc////////////////////////////////////////////////////////////////////////
template <typename A, unsigned B>
constexpr bool is_negative(intt<A, B> const& a) noexcept
{
  return a[B - 1] >> (intt<A, B>::bits_e - 1);
}

//
template <typename T, unsigned N>
auto to_raw(intt<T, N> const& a) noexcept
{
  std::stringstream ss;

  ss << std::hex;

  for (auto i(N - 1); i; --i)
  {
    ss << a[i] << " ";
  }

  ss << a[0];

  return ss.str();
}

template <typename T, unsigned N>
std::string to_string(intt<T, N> a)
{
  auto const neg(is_negative(a));

  std::string r;

  do
  {
    std::int8_t const d(a % 10);

    r.insert(0, 1, '0' + (neg ? -d : d));

    a /= 10;
  }
  while (a);

  if (neg)
  {
    r.insert(0, 1, '-');
  }

  return r;
}

template <typename A, unsigned B>
inline auto& operator<<(std::ostream& os, intt<A, B> const& p)
{
  return os << to_string(p);
}

}

namespace std
{

template <typename T, unsigned N>
struct hash<intt::intt<T, N>>
{
  auto operator()(intt::intt<T, N> const& a) const noexcept
  {
    return [&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
      {
        std::size_t seed{672807365};

        (
          (
            seed ^= hash<T>()(a[I]) + 0x9e3779b9 + (seed << 6) + (seed >> 2)
          ),
          ...
        );

        return seed;
      }(std::make_index_sequence<N>());
  }
};

}

#endif // LONGINT_HPP
