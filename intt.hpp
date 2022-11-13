#ifndef INTT_HPP
# define INTT_HPP
# pragma once

#include <climits> // CHAR_BIT
#include <cmath> // std::pow()
#include <concepts> // std::floating_point, std::integral

#include <array> // std::array
#include <algorithm> // std::max()
#include <iomanip> // std::hex
#include <ostream> // std::ostream
#include <sstream> // std::stringstream
#include <utility> // std::pair
#include <type_traits>

namespace intt
{

struct direct{};

namespace detail
{

template <typename U>
static constexpr auto bit_size_v(CHAR_BIT * sizeof(U));

template <typename T, auto = std::is_enum_v<T>>
struct underlying_type : std::underlying_type<T> {};

template <typename T>
struct underlying_type<T, false> { using type = T; };

template <typename T>
using underlying_type_t = typename underlying_type<T>::type;

}

template <std::unsigned_integral T, std::size_t N> requires(N > 0)
struct intt
{
  enum : std::size_t { wbits = sizeof(T) * CHAR_BIT }; // bits per word

  using value_type = T;

  std::array<T, N> v_;

  intt() = default;

  intt(intt const&) = default;
  intt(intt&&) = default;

  constexpr intt(direct, auto&& ...a) noexcept: v_{a...} { }

  template <std::floating_point U>
  intt(U f) noexcept
  {
    if (f = std::trunc(f); f < U{})
    {
      f = -f;

      [&]<typename V, auto ...I>(std::integer_sequence<V, I...>) noexcept
      {
        (
          (
            v_[I] = ~T(f * std::pow(U(2), -I * wbits))
          ),
          ...
        );

        bool c{true};

        (
          [&]() noexcept
          {
            auto& a(v_[I]);

            a += c;
            c = a < c;
          }(),
          ...
        );
      }(std::make_integer_sequence<int, N>());
    }
    else
    {
      [&]<typename V, auto ...I>(std::integer_sequence<V, I...>) noexcept
      {
        (
          (
            v_[I] = T(f * std::pow(U(2), -I * wbits))
          ),
          ...
        );
      }(std::make_integer_sequence<int, N>());
    }
  }

  template <typename U> requires(std::is_integral_v<U> || std::is_enum_v<U>)
  constexpr intt(U const v) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      if constexpr(std::is_signed_v<detail::underlying_type_t<U>>)
      { // v_[0] is lsw, v_[N - 1] msw
        auto const neg(v < 0);

        (
          (
            v_[I] = I * wbits < detail::bit_size_v<U> ?
              v >> I * wbits :
              neg ? ~T{} : T{}
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

  template <std::size_t M>
  constexpr intt(intt<T, M> const& o) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      auto const neg(is_neg(o));

      (
        [&]() noexcept
        {
          if constexpr(I < M)
          {
            v_[I] = o.v_[I];
          }
          else
          {
            v_[I] = neg ? ~T{} : T{};
          }
        }(),
        ...
      );
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
        { // words shifted to the left
          return ((U(v_[I]) << I * wbits) | ...);
        }
        else
        {
          return v_.front();
        }
      }(std::make_index_sequence<detail::bit_size_v<U> / wbits>());
  }

  //
  static constexpr auto size() noexcept { return N; }

  constexpr auto data() const noexcept { return v_.data(); }

  // bit access
  template <std::size_t I>
  constexpr bool bit() const noexcept
  {
    return v_[I / wbits] & (T{1} << (I % wbits));
  }

  template <std::size_t I>
  constexpr void clear_bit() noexcept
  {
    v_[I / wbits] &= T(~(T{1} << (I % wbits)));
  }

  template <std::size_t I>
  constexpr void set_bit() noexcept
  {
    v_[I / wbits] |= T{1} << (I % wbits);
  }

  // member access
  constexpr T operator[](std::size_t const i) const noexcept { return v_[i]; }

  // bitwise
  constexpr auto operator~() const noexcept
  {
    return ([&]<auto ...I>(std::index_sequence<I...>) noexcept -> intt
      {
        return {direct{}, T(~v_[I])...};
      }
    )(std::make_index_sequence<N>());
  }

  #define INTT_BITWISE(OP)\
  constexpr auto operator OP(intt const& o) const noexcept\
  {\
    return ([&]<auto ...I>(std::index_sequence<I...>) noexcept -> intt\
      {\
        return {direct{}, T(v_[I] OP o.v_[I])...};\
      }\
    )(std::make_index_sequence<N>());\
  }

  INTT_BITWISE(&)
  INTT_BITWISE(|)
  INTT_BITWISE(^)

  constexpr auto operator<<(std::integral auto M) const noexcept
  {
    auto r(*this);

    if (M)
    {
      auto const shl([&]<auto ...I>(std::size_t const e,
        std::index_sequence<I...>) noexcept
        {
          (
            (
              r.v_[N - 1 - I] =
                (r.v_[N - 1 - I] << e) | (r.v_[N - 1 - I - 1] >> (wbits - e))
            ),
            ...
          );

          r.v_.front() <<= e;
        }
      );

      for (; M > wbits - 1; M -= wbits - 1)
      {
        shl.template operator()(wbits - 1, std::make_index_sequence<N - 1>());
      }

      shl.template operator()(M, std::make_index_sequence<N - 1>());
    }

    return r;
  }

  constexpr auto operator>>(std::integral auto M) const noexcept
  {
    auto r(*this);

    if (M)
    {
      auto const shr([neg(is_neg(*this)), &r]<auto ...I>(std::size_t const e,
        std::index_sequence<I...>) noexcept
        {
          (
            (
              r.v_[I] = (r.v_[I] >> e) | (r.v_[I + 1] << (wbits - e))
            ),
            ...
          );

          r.v_[N - 1] = (r.v_[N - 1] >> e) | (neg ? ~T{} << (wbits - e) : T{});
        }
      );

      for (; M > wbits - 1; M -= wbits - 1)
      {
        shr.template operator()(wbits - 1, std::make_index_sequence<N - 1>());
      }

      shr.template operator()(M, std::make_index_sequence<N - 1>());
    }

    return r;
  }

  constexpr auto lshr(std::size_t M) const noexcept
  {
    auto r(*this);

    if (M)
    {
      auto const shr([neg(is_neg(*this)), &r]<auto ...I>(std::size_t const e,
        std::index_sequence<I...>) noexcept
        {
          (
            (
              r.v_[I] = (r.v_[I] >> e) | (r.v_[I + 1] << (wbits - e))
            ),
            ...
          );

          r.v_[N - 1] >>= e;
        }
      );

      for (; M > wbits - 1; M -= wbits - 1)
      {
        shr.template operator()(wbits - 1, std::make_index_sequence<N - 1>());
      }

      shr.template operator()(M, std::make_index_sequence<N - 1>());
    }

    return r;
  }

  constexpr auto wshl(std::size_t const n) const noexcept
  {
    intt<T, N> r;

    for (std::size_t i{n}; i < N; ++i)
    {
      r.v_[i] = v_[i - n];
    }

    auto const e(std::min(N, n));

    for (std::size_t i{}; i != e; ++i)
    {
      r.v_[i] = {};
    }

    return r;
  }

  constexpr auto lshifted() const noexcept
  {
    intt<T, 2 * N> r;

    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      (
        (
          [&]() noexcept
          {
            if constexpr(I >= N)
            {
              r.v_[I] = v_[I - N];
            }
            else
            {
              r.v_[I] = {};
            }
          }()
        ),
        ...
      );
    }(std::make_index_sequence<2 * N>());

    return r;
  }

  constexpr auto rshifted() const noexcept
  {
    intt<T, N / 2> r;

    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      ((r.v_[I] = v_[N / 2 + I]), ...);
    }(std::make_index_sequence<N / 2>());

    return r;
  }

  // increment, decrement
  constexpr auto& operator++() noexcept
  {
    return *this += intt(direct{}, T(1));
  }

  constexpr auto& operator--() noexcept
  {
    return *this -= intt(direct{}, T(1));
  }

  constexpr auto operator++(int) const noexcept
  {
    auto const r(*this); ++*this; return r;
  }

  constexpr auto operator--(int) const noexcept
  {
    auto const r(*this); --*this; return r;
  }

  //
  constexpr auto operator+() const noexcept { return *this; }

  constexpr auto operator-() const noexcept
  {
    auto r(*this);

    r.negate();

    return r;
  }

  //
  constexpr auto operator+(intt const& o) const noexcept
  {
    intt<T, N> r;

    [&]<std::size_t ...I>(std::index_sequence<I...>) noexcept
    {
      bool c{};

      (
        [&]() noexcept
        {
          auto& s(r.v_[I]);
          auto const& a(v_[I]);

          s = a + c + o.v_[I];
          c = c ? s <= a : s < a;
        }(),
        ...
      );
    }(std::make_index_sequence<N>());

    return r;
  }

  constexpr auto operator-(intt const& o) const noexcept { return *this +-o; }

  constexpr auto operator*(intt const& o) const noexcept
  {
    return intt<T, N>(mul(o));
  }

  constexpr auto operator/(intt const& o) const noexcept
  {
    return std::get<0>(div(o));
  }

  constexpr auto operator%(intt const& o) const noexcept
  {
    return std::get<1>(div(o));
  }

  constexpr auto div(intt const& o) const noexcept
  {
    intt<T, 2 * N> r(*this);
    auto D(o.lshifted());

    auto const neg(is_neg(*this));

    if (neg) r.negate();
    r <<= 1;

    if (is_neg(o)) D.negate();

    intt q{};

    //
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      (
        [&]() noexcept
        {
          if ((r <<= 1) >= D)
          {
            r -= D;

            q.set_bit<wbits * N - 2 - I>();
          }
        }(),
        ...
      );
    }(std::make_index_sequence<wbits * N - 1>());

    //
    return std::pair(
      neg ^ is_neg(o) ? -q : q,
      neg ? -r.rshifted() : r.rshifted()
    );
  }

  constexpr auto mul(intt const& o) const noexcept
  {
    intt<T, 2 * N> r{}, A{this->lshifted()};

    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      (
        [&]() noexcept
        {
          if (o.bit<I>())
          {
            r += A;
          }

          r >>= 1;
        }(),
        ...
      );
    }(std::make_index_sequence<wbits * N - 1>());

    if (is_neg(o))
    {
      r -= A;
    }

    return r >> 1;
  }

  constexpr void negate() noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      ((v_[I] = T(~v_[I])), ...);

      bool c{true};

      (
        [&]() noexcept
        {
          auto& a(v_[I]);

          a += c;
          c = a < c;
        }(),
        ...
      );
    }(std::make_index_sequence<N>());
  }

  //
  constexpr auto operator==(intt<T, N> const& o) const noexcept
  {
    return [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        return ((v_[N - 1 - I] == o.v_[N - 1 - I]) && ...);
      }(std::make_index_sequence<N>());
  }

  constexpr auto operator<=>(intt<T, N> const& o) const noexcept
  {
    if (auto const nega(is_neg(*this)), negb(is_neg(o)); nega != negb)
    {
      return nega && !negb ?
        std::strong_ordering::less:
        std::strong_ordering::greater;
    }
    else
    {
      std::size_t i{N};

      do
      {
        --i;

        if (auto const c(v_[i] <=> o.v_[i]); c < 0)
        {
          return std::strong_ordering::less;
        }
        else if (c > 0)
        {
          return std::strong_ordering::greater;
        }
      }
      while (i);
    }

    return std::strong_ordering::equal;
  }

  //
  static constexpr auto max() noexcept { return -++min(); }
  static constexpr auto min() noexcept { return intt(1) << (N * wbits) - 1; }
};

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
  return a.template bit<N * intt<T, N>::wbits - 1>();
}

template <typename T, std::size_t N>
constexpr auto sqrt(intt<T, N> const& a) noexcept
{
  intt<T, 2 * N> r(a);
  r <<= 1;

  intt<T, N> q{};

  //
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      [&]() noexcept
      {
        q.template set_bit<intt<T, N>::wbits * N - 2 - I>();

        if (auto const Q(q.lshifted()); (r <<= 1) >= Q)
        {
          r -= Q;
        }
        else
        {
          q.template clear_bit<intt<T, N>::wbits * N - 2 - I>();
        }
      }(),
      ...
    );
  }(std::make_index_sequence<intt<T, N>::wbits * N - 1>());

  //
  return q;
}

//
template <typename T, std::size_t N>
auto to_raw(intt<T, N> const& a) noexcept
{
  using U = std::conditional_t<std::is_same_v<T, std::uint8_t>, unsigned, T>;

  std::stringstream ss;

  ss << '"' << std::hex << std::setfill('0');

  for (auto i(N - 1); i; --i)
  {
    ss << std::setw(2) << U(a[i]) << " ";
  }

  ss << std::setw(2) << U(a[0]) << '"';

  return ss.str();
}

template <typename T, std::size_t N>
std::string to_string(intt<T, N> a)
{
  std::string r;

  auto const neg(is_neg(a));

  do
  {
    auto const p(a.div({direct{}, T(10)}));

    signed char const d(std::get<1>(p));

    r.insert(0, 1, '0' + (neg ? -d : d));

    a = std::get<0>(p);
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
