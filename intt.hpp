#ifndef LONGINT_HPP
# define LONGINT_HPP
# pragma once

#include <cassert>
#include <climits>

#include <array>
#include <ostream>
#include <sstream>
#include <utility>
#include <type_traits>

namespace intt
{

namespace detail
{

template <typename U>
static constexpr auto bit_size_v(CHAR_BIT * sizeof(U));

template <typename U>
static constexpr U min_v(
  std::is_signed_v<U> ? U{1} << (bit_size_v<U> - 1) : U{}
);

template <typename U>
static constexpr U max_v(
  std::is_signed_v<U> ? -(min_v<U> + U(1)) : ~U{}
);

}

template <typename T, unsigned N>
class intt
{
  static_assert(std::is_unsigned_v<T>);
  static_assert(N > 0);

public:
  using value_type = std::array<T, N>;

  value_type v_;

public:
  enum : unsigned { size = N };

  enum : unsigned { bits_e = sizeof(T) * CHAR_BIT };
  enum : unsigned { bits = N * bits_e };

  enum : T { max_e = detail::max_v<T> };

  intt() = default;

  intt(intt const&) = default;
  intt(intt&&) = default;

  constexpr intt(decltype(v_)&& v) noexcept : v_(std::move(v)) { }

  template <typename U> requires(std::is_integral_v<U>)
  constexpr intt(U const v) noexcept
  {
    [&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
    {
      if constexpr(std::is_signed_v<U>)
      { // v_[0] is least significant, v_[N - 1] most significant
        (
          (
            v_[I] = I * bits_e < detail::bit_size_v<U> ?
              v >> I * bits_e :
              v >= U{} ? T{} : ~T{}
          ),
          ...
        );
      }
      else
      {
        (
          (
            v_[I] = I * bits_e < detail::bit_size_v<U> ?
              v >> I * bits_e :
              T{}
          ),
          ...
        );
      }
    }(std::make_index_sequence<N>());
  }

  // assignment
  intt& operator=(intt const&) = default;
  intt& operator=(intt&&) = default;

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
  INTT_ASSIGNMENT(%)
  INTT_ASSIGNMENT(&)
  INTT_ASSIGNMENT(|)
  INTT_ASSIGNMENT(^)

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
    return [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        return (v_[I] || ...);
      }(std::make_index_sequence<N>());
  }

  template <typename U> requires(std::is_integral_v<U>)
  constexpr explicit operator U() const noexcept
  {
    return [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        if constexpr(bool(sizeof...(I)))
        {
          return (
            (U(v_[I]) << I * bits_e) |
            ...
          );
        }
        else
        {
          return v_.front();
        }
      }(std::make_index_sequence<detail::bit_size_v<U> / bits_e>());
  }

  // member access
  constexpr auto& operator*() noexcept { return v_.front(); }
  constexpr auto& operator*() const noexcept { return v_.front(); }

  constexpr auto operator[](unsigned const i) const noexcept { return v_[i]; }

  //
  constexpr auto operator~() const noexcept
  {
    return ([&]<auto ...I>(std::index_sequence<I...>) noexcept -> intt
      {
        return {value_type{T(~v_[I])...}};
      }
    )(std::make_index_sequence<N>());
  }

  #define INTT_BITWISE(OP)\
  constexpr auto operator OP(intt const& o) const noexcept\
  {\
    return ([&]<auto ...I>(std::index_sequence<I...>) noexcept -> intt\
      {\
        return {value_type{(v_[I] OP o[I])...}};\
      }\
    )(std::make_index_sequence<N>());\
  }

  INTT_BITWISE(&)
  INTT_BITWISE(|)
  INTT_BITWISE(^)

  constexpr auto operator<<(unsigned M) const noexcept
  {
    auto r(*this);

    auto const shl([&r]<std::size_t ...I>(unsigned const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            r.v_[N - 1 - I] =
              (r[N - 1 - I] << e) | (r[N - 1 - I - 1] >> (bits_e - e))
          ),
          ...
        );

        *r <<= e;
      }
    );

    for (; M >= bits_e; M -= bits_e)
    {
      shl.template operator()(bits_e, std::make_index_sequence<N - 1>());
    }

    shl.template operator()(M, std::make_index_sequence<N - 1>());

    return r;
  }

  constexpr auto operator>>(unsigned M) const noexcept
  {
    auto r(*this);

    auto const shr([neg(is_negative(*this)), &r]<auto ...I>(unsigned const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            r.v_[I] = (r[I] >> e) | (r[I + 1] << (bits_e - e))
          ),
          ...
        );

        r.v_[N - 1] =
          (r.v_[N - 1] >> e) | (neg ? ~T{} << (bits_e - e) : T{});
      }
    );

    for (; M >= bits_e; M -= bits_e)
    {
      shr.template operator()(bits_e, std::make_index_sequence<N - 1>());
    }

    shr.template operator()(M, std::make_index_sequence<N - 1>());

    return r;
  }

  // increment, decrement
  constexpr auto& operator++() noexcept { return *this += 1; }
  constexpr auto& operator--() noexcept { return *this -= 1; }

  constexpr auto operator++(int) const noexcept { return *this + 1; }
  constexpr auto operator--(int) const noexcept { return *this - 1; }

  //
  constexpr auto operator+() const noexcept { return *this; }
  constexpr auto operator-() const noexcept { return ~*this + 1; }

  //
  constexpr auto operator+(intt const& o) const noexcept
  {
    return ([&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
      {
        intt<T, N> r;

        bool c{};

        (
          (
            r.v_[I] = v_[I] + o[I] + c,
            c = v_[I] > max_e - o[I] - c
          ),
          ...
        );

        return r;
      }
    )(std::make_index_sequence<N>());
  }

  constexpr auto operator-(intt const& o) const noexcept
  {
    return *this + (-o);
  }

  constexpr auto operator*(intt const& o) const noexcept
  {
    return [&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
      {
        return (
            [&]<auto J>() noexcept
            {
              return (
                (
                  intt(v_[J] * o[I]) << (I + J) * bits_e
                ) +
                ...
              );
            }.template operator()<I>() +
            ...
          );
      }(std::make_index_sequence<N>());
  }

  constexpr auto operator%(intt const& o) const noexcept
  {
    return *this - (*this / o) * o;
  }
};

//arithmetic//////////////////////////////////////////////////////////////////

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

//comparison//////////////////////////////////////////////////////////////////
template <typename A, unsigned B>
constexpr auto operator==(intt<A, B> const& a, intt<A, B> const& b) noexcept
{
  return a.v_ == b.v_;
}

template <typename A, unsigned B>
constexpr auto operator<(intt<A, B> const& a, intt<A, B> const& b) noexcept
{
  return is_negative(a - b);
}

template <typename A, unsigned B>
constexpr auto operator<=>(intt<A, B> const& a, intt<A, B> const& b) noexcept
{
  return a == b ?
    std::strong_ordering::equal :
    a < b ? std::strong_ordering::less : std::strong_ordering::greater;
}

// conversions
#define INTT_LEFT_CONVERSION(OP)\
template <typename A, unsigned B, typename U>\
constexpr auto operator OP (U&& a, intt<A, B> const& b) noexcept\
  requires(std::is_arithmetic_v<std::remove_cvref_t<U>>)\
{\
  return intt<A, B>(std::forward<U>(a)) OP b;\
}

INTT_LEFT_CONVERSION(+)
INTT_LEFT_CONVERSION(-)
INTT_LEFT_CONVERSION(*)
INTT_LEFT_CONVERSION(/)
INTT_LEFT_CONVERSION(%)
INTT_LEFT_CONVERSION(==)
INTT_LEFT_CONVERSION(!=)
INTT_LEFT_CONVERSION(<)
INTT_LEFT_CONVERSION(<=)
INTT_LEFT_CONVERSION(>)
INTT_LEFT_CONVERSION(>=)
INTT_LEFT_CONVERSION(<=>)

#define INTT_RIGHT_CONVERSION(OP)\
template <typename A, unsigned B, typename U>\
constexpr auto operator OP (intt<A, B> const& a, U&& b) noexcept\
  requires(std::is_arithmetic_v<std::remove_cvref_t<U>>)\
{\
  return a OP intt<A, B>(std::forward<U>(b));\
}

INTT_RIGHT_CONVERSION(+)
INTT_RIGHT_CONVERSION(-)
INTT_RIGHT_CONVERSION(*)
INTT_RIGHT_CONVERSION(/)
INTT_RIGHT_CONVERSION(%)
INTT_RIGHT_CONVERSION(==)
INTT_RIGHT_CONVERSION(!=)
INTT_RIGHT_CONVERSION(<)
INTT_RIGHT_CONVERSION(<=)
INTT_RIGHT_CONVERSION(>)
INTT_RIGHT_CONVERSION(>=)
INTT_RIGHT_CONVERSION(<=>)

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

  if constexpr(std::is_same_v<T, std::uint8_t>)
    for (auto i(N - 1); i; --i) ss << unsigned(a[i]) << " ";
  else
    for (auto i(N - 1); i; --i) ss << a[i] << " ";

  if constexpr(std::is_same_v<T, std::uint8_t>)
    ss << unsigned(*a);
  else
    ss << *a;

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

        return (
          (
            seed ^= hash<T>()(a[I]) + 0x9e3779b9 + (seed << 6) + (seed >> 2)
          ),
          ...
        );
      }(std::make_index_sequence<N>());
  }
};

}

#endif // LONGINT_HPP
