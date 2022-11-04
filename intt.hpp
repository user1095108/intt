#ifndef INTT_HPP
# define INTT_HPP
# pragma once

#include <climits>
#include <cmath> // std::pow()
#include <concepts>

#include <array>
#include <algorithm>
#include <iomanip> // std::hex
#include <ostream>
#include <utility> // std::pair
#include <type_traits>

namespace intt
{

struct direct{};

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

template <std::unsigned_integral T, std::size_t N> requires(N > 0)
struct intt
{
  std::array<T, N> v_;

  enum : std::size_t { size = N }; // number of words

  enum : std::size_t { wbits = sizeof(T) * CHAR_BIT }; // bits per word
  enum : std::size_t { bits = N * wbits }; // size in bits

  enum : T { wmax = detail::max_v<T> };

  intt() = default;

  intt(intt const&) = default;
  intt(intt&&) = default;

  constexpr intt(direct, std::integral auto const ...a) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      ((v_[I] = a), ...);
    }(std::make_index_sequence<std::min(N, sizeof...(a))>());
  }

  template <typename U> requires(std::is_integral_v<U> || std::is_enum_v<U>)
  constexpr intt(U const v) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      if constexpr(std::is_signed_v<U>)
      { // v_[0] is lsw, v_[N - 1] msw
        (
          (
            v_[I] = I * wbits < detail::bit_size_v<U> ?
              v >> I * wbits :
              v >= U{} ? T{} : ~T{}
          ),
          ...
        );
      }
      else
      {
        (
          (
            v_[I] = I * wbits < detail::bit_size_v<U> ?
              v >> I * wbits :
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

  constexpr auto& operator<<=(std::integral auto const i) noexcept
  {
    return *this = *this << i;
  }

  constexpr auto& operator>>=(std::integral auto const i) noexcept
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

  template <std::floating_point U>
  explicit operator U() const noexcept
  {
    if (is_neg(*this))
    {
      return [&]<auto ...I>(std::index_sequence<I...>) noexcept
        {
          return -(((T(~v_[I]) * std::pow(U(2), I * wbits)) + ...) + U{1});
        }(std::make_index_sequence<N>());
    }
    else
    {
      return [&]<auto ...I>(std::index_sequence<I...>) noexcept
        {
          return ((v_[I] * std::pow(U(2), I * wbits)) + ...);
        }(std::make_index_sequence<N>());
    }
  }

  template <std::integral U>
  constexpr operator U() const noexcept
  {
    return [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        if constexpr(bool(sizeof...(I)))
        {
          return ((U(v_[I]) << I * wbits) | ...);
        }
        else
        {
          return v_.front();
        }
      }(std::make_index_sequence<detail::bit_size_v<U> / wbits>());
  }

  // member access
  constexpr T operator[](std::size_t const i) const noexcept { return v_[i]; }

  // bitwise
  constexpr auto operator~() const noexcept
  {
    return ([&]<auto ...I>(std::index_sequence<I...>) noexcept -> intt
      {
        return {direct{}, ~v_[I]...};
      }
    )(std::make_index_sequence<N>());
  }

  #define INTT_BITWISE(OP)\
  constexpr auto operator OP(intt const& o) const noexcept\
  {\
    return ([&]<auto ...I>(std::index_sequence<I...>) noexcept -> intt\
      {\
        return {direct{}, (v_[I] OP o[I])...};\
      }\
    )(std::make_index_sequence<N>());\
  }

  INTT_BITWISE(&)
  INTT_BITWISE(|)
  INTT_BITWISE(^)

  constexpr auto operator<<(std::integral auto M) const noexcept
  {
    auto r(*this);

    auto const shl([&]<auto ...I>(std::size_t const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            r.v_[N - 1 - I] =
              (r[N - 1 - I] << e) | (r[N - 1 - I - 1] >> (wbits - e))
          ),
          ...
        );

        r.v_.front() <<= e;
      }
    );

    for (; M >= wbits - 1; M -= wbits - 1)
    {
      shl.template operator()(wbits - 1, std::make_index_sequence<N - 1>());
    }

    shl.template operator()(M, std::make_index_sequence<N - 1>());

    return r;
  }

  constexpr auto operator>>(std::integral auto M) const noexcept
  {
    auto r(*this);

    auto const shr([&]<auto ...I>(std::size_t const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            r.v_[I] = (r[I] >> e) | (r[I + 1] << (wbits - e))
          ),
          ...
        );

        r.v_[N - 1] = (r.v_[N - 1] >> e) |
          (is_neg(*this) ? ~T{} << (wbits - e) : T{});
      }
    );

    for (; M >= wbits - 1; M -= wbits - 1)
    {
      shr.template operator()(wbits - 1, std::make_index_sequence<N - 1>());
    }

    shr.template operator()(M, std::make_index_sequence<N - 1>());

    return r;
  }

  // increment, decrement
  constexpr auto& operator++() noexcept { return *this += T(1); }
  constexpr auto& operator--() noexcept { return *this -= T(1); }

  constexpr auto operator++(int) const noexcept { return *this + T(1); }
  constexpr auto operator--(int) const noexcept { return *this - T(1); }

  //
  constexpr auto operator+() const noexcept { return *this; }
  constexpr auto operator-() const noexcept { return ~*this + T(1); }

  //
  constexpr auto add(intt const& o, bool c = {}) const noexcept
  {
    return std::pair{
        [&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
        {
          intt<T, N> r;

          (
            (
              r.v_[I] = v_[I] + o.v_[I] + c,
              c = c ? r.v_[I] <= v_[I] : r.v_[I] < v_[I]
            ),
            ...
          );

          return r;
        }(std::make_index_sequence<N>()),
        c
      };
  }

  constexpr auto div(intt const& o) const noexcept
  {
    auto a(is_neg(o) ? -*this : *this);
    auto b(is_neg(o) ? -o : o); // b is positive

    intt q{};

    if (is_neg(a))
    {
      a = -a;

      while (a >= b)
      {
        a -= b;

        --q;
      }
    }
    else
    {
      while (a >= b)
      {
        a -= b;

        ++q;
      }
    }

    return std::pair(q, a);
  }

  //
  constexpr auto operator+(intt const& o) const noexcept
  {
    return std::get<0>(add(o));
  }

  constexpr auto operator-(intt const& o) const noexcept { return *this +-o; }

  constexpr auto operator*(intt const& o) const noexcept
  {
    return [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        return (
            [&]<auto J>() noexcept
            {
              return (
                (
                  intt(v_[I] * o.v_[J]) << (I + J) * wbits
                ) +
                ...
              );
            }.template operator()<I>() +
            ...
          );
      }(std::make_index_sequence<N>());
  }

  constexpr auto operator/(intt const& o) const noexcept
  {
    return std::get<0>(div(o));
  }

  constexpr auto operator%(intt const& o) const noexcept
  {
    return std::get<1>(div(o));
  }
};

//comparison//////////////////////////////////////////////////////////////////
template <typename A, std::size_t B>
constexpr auto operator==(intt<A, B> const& a, intt<A, B> const& b) noexcept
{
  return a.v_ == b.v_;
}

template <typename A, std::size_t B>
constexpr auto operator<(intt<A, B> const& a, intt<A, B> const& b) noexcept
{
  return is_neg(a - b);
}

template <typename A, std::size_t B>
constexpr auto operator>(intt<A, B> const& a, intt<A, B> const& b) noexcept
{
  return is_neg(b - a);
}

template <typename A, std::size_t B>
constexpr auto operator<=(intt<A, B> const& a, intt<A, B> const& b) noexcept
{
  return !(a > b);
}

template <typename A, std::size_t B>
constexpr auto operator>=(intt<A, B> const& a, intt<A, B> const& b) noexcept
{
  return !(a < b);
}

template <typename A, std::size_t B>
constexpr auto operator<=>(intt<A, B> const& a, intt<A, B> const& b) noexcept
{
  return a == b ?
    std::strong_ordering::equal :
    a < b ? std::strong_ordering::less : std::strong_ordering::greater;
}

// conversions
#define INTT_LEFT_CONVERSION(OP)\
template <typename A, std::size_t B, typename U>\
constexpr auto operator OP (U&& a, intt<A, B> const& b) noexcept\
  requires(std::is_enum_v<std::remove_cvref_t<U>> ||\
    std::is_arithmetic_v<std::remove_cvref_t<U>>)\
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
template <typename A, std::size_t B, typename U>\
constexpr auto operator OP (intt<A, B> const& a, U&& b) noexcept\
  requires(std::is_enum_v<std::remove_cvref_t<U>> ||\
    std::is_arithmetic_v<std::remove_cvref_t<U>>)\
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
template <typename T, std::size_t N>
constexpr bool is_neg(intt<T, N> const& a) noexcept
{
  return a[N - 1] >> (intt<T, N>::wbits - 1);
}

//
template <typename T, std::size_t N>
auto to_raw(intt<T, N> const& a) noexcept
{
  using U = std::conditional_t<std::is_same_v<T, std::uint8_t>, unsigned, T>;

  std::stringstream ss;

  ss << std::hex << std::setfill('0');

  for (auto i(N - 1); i; --i)
  {
    ss << std::setw(2) << U(a[i]) << " ";
  }

  ss << std::setw(2) << U(a[0]);

  return ss.str();
}

template <typename T, std::size_t N>
std::string to_string(intt<T, N> a)
{
  auto const neg(is_neg(a));

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

template <typename T, std::size_t N>
inline auto& operator<<(std::ostream& os, intt<T, N> const& p)
{
  return os << to_string(p);
}

}

namespace std
{

template <typename T, std::size_t N>
struct hash<intt::intt<T, N>>
{
  auto operator()(intt::intt<T, N> const& a) const noexcept
  {
    return [&]<auto ...I>(std::index_sequence<I...>) noexcept
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

#endif // INTT_HPP
