#ifndef INTT_HPP
# define INTT_HPP
# pragma once

#include <cassert>
#include <climits> // CHAR_BIT
#include <cmath> // std::ldexp()
#include <concepts> // std::floating_point, std::integral

#include <algorithm> // std::max()
#include <bit>
#include <iomanip> // std::hex
#include <iterator>
#include <ostream> // std::ostream
#include <sstream> // std::stringstream
#include <utility> // std::pair
#include <type_traits>

namespace intt
{

struct direct{};
struct direct2{};

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

  T v_[N];

  intt() = default;

  intt(intt const&) = default;
  intt(intt&&) = default;

  constexpr intt(direct, auto&& ...a) noexcept: v_{a...} { }

  constexpr intt(direct2, std::size_t const i, auto&& ...a) noexcept
    requires(
      std::conjunction_v<std::is_same<T, std::remove_cvref_t<decltype(a)>>...>
    )
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      auto const select([](std::size_t const i, auto&& ...a) noexcept
        {
          return [&]<auto ...J>(std::index_sequence<J...>) noexcept
          {
            T r;

            (void)(((J == i) && (r = a, true)) || ...);

            return r;
          }(std::make_index_sequence<sizeof...(a)>());
        }
      );

      (
        (
          v_[I] = I >= i ?
            I - i >= sizeof...(a) ? T{} : select(I - i, a...) :
            T{}
        ),
        ...
      );
    }(std::make_index_sequence<N>());
  }

  template <std::floating_point U>
  constexpr intt(U f) noexcept
  {
    if (f = std::trunc(f); f < U{})
    {
      f = -f;

      [&]<typename V, V ...I>(std::integer_sequence<V, I...>) noexcept
      {
        (
          [&]() noexcept
          {
            auto const tmp(std::ldexp(f, -V(wbits)));

            v_[I] = ~T(std::ldexp(tmp - (f = std::trunc(tmp)), wbits));
          }(),
          ...
        );

        bool c{true};

        ((v_[I] += c, c = v_[I] < c), ...);
      }(std::make_integer_sequence<int, N>());
    }
    else
    {
      [&]<typename V, V ...I>(std::integer_sequence<V, I...>) noexcept
      {
        (
          [&]() noexcept
          {
            auto const tmp(std::ldexp(f, -V(wbits)));

            v_[I] = std::ldexp(tmp - (f = std::trunc(tmp)), wbits);
          }(),
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

  template <std::size_t M>
  constexpr intt(intt<T, M> const& o, direct) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      (
        [&]() noexcept
        {
          if constexpr(I < M)
          {
            v_[I] = o.v_[I];
          }
          else
          {
            v_[I] = {};
          }
        }(),
        ...
      );
    }(std::make_index_sequence<N>());
  }

  template <typename U, std::size_t M>
  constexpr intt(intt<U, M> const& o) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      auto const neg(is_neg(o));

      (
        (
          v_[I] = I * wbits < M * intt<U, M>::wbits ?
            T(o >> I * wbits) :
            neg ? ~T{} : T{}
        ),
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
          return -(((T(~v_[I]) * std::ldexp(U(1), I * wbits)) + ...) + U{1});
        }(std::make_index_sequence<N>());
    }
    else
    {
      return [&]<auto ...I>(std::index_sequence<I...>) noexcept
        {
          return ((v_[I] * std::ldexp(U(1), I * wbits)) + ...);
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
          return *v_;
        }
      }(std::make_index_sequence<detail::bit_size_v<U> / wbits>());
  }

  //
  constexpr T operator[](std::size_t const i) const noexcept { return v_[i]; }

  //
  static constexpr auto size() noexcept { return N; }

  constexpr auto data() const noexcept { return v_; }

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
      auto const shl([&]<auto ...I>(auto const e,
        std::index_sequence<I...>) noexcept
        {
          (
            (
              r.v_[N - 1 - I] = (r.v_[N - 1 - I] << e) |
                (r.v_[N - 1 - I - 1] >> (wbits - e))
            ),
            ...
          );

          *r.v_ <<= e;
        }
      );

      for (; std::size_t(M) >= wbits; M -= wbits - 1)
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
      auto const shr([neg(is_neg(*this)), &r]<auto ...I>(auto const e,
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

      for (; std::size_t(M) >= wbits; M -= wbits - 1)
      {
        shr.template operator()(wbits - 1, std::make_index_sequence<N - 1>());
      }

      shr.template operator()(M, std::make_index_sequence<N - 1>());
    }

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

    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      ((r.v_[I] = T(~r.v_[I])), ...);

      bool c{true};

      ((r.v_[I] += c, c = r.v_[I] < c), ...);
    }(std::make_index_sequence<N>());

    return r;
  }

  //
  constexpr auto operator+(intt const& o) const noexcept
  {
    intt<T, N> r;

    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      bool c{};

      (
        [&]() noexcept
        {
          auto& s(r.v_[I]);
          auto const& a(v_[I]);

          s = c + a + o.v_[I];
          c = c ? s <= a : s < a;
        }(),
        ...
      );
    }(std::make_index_sequence<N>());

    return r;
  }

  constexpr auto operator-(intt const& o) const noexcept { return *this +-o; }

  /*
  constexpr auto operator*(intt const& o) const noexcept
  {
    intt<T, 2 * N> r{}, A{lshifted(*this)};

    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      (
        [&]() noexcept
        {
          if (test_bit<I>(o))
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

    return intt(r >> 1, direct{});
  }
  */

  constexpr intt operator*(intt const& o) const noexcept
  {
    auto const nega(is_neg(*this)), negb(is_neg(o));

    intt r{};

    if constexpr(std::is_same_v<T, std::uint64_t>)
    { // multiplying half-words, wbits per iteration
      using H = std::conditional_t<
        std::is_same_v<T, std::uint64_t>,
        std::uint32_t,
        std::conditional_t<
          std::is_same_v<T, std::uint16_t>,
          std::uint8_t,
          std::uint8_t
        >
      >;

      enum : size_t { M = 2 * N, hwbits = wbits / 2 };

      for (std::size_t i{}; M != i; ++i)
      { // detail::bit_size_v<H> * (i + j) < wbits * N
        std::size_t S(i), j{};

        do
        {
          T pp;

          {
            H const a(v_[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0));
            H const b(o.v_[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0));
            pp = T(nega ? H(~a) : a) * (negb ? H(~b) : b);
          }

          r += intt(direct2{}, S / 2, pp) <<
            (S % 2 ? std::size_t(hwbits) : 0);
        }
        while (++j, M != ++S);
      }
    }
    else
    { // multiplying words, 2 * wbits per iteration
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

      for (std::size_t i{}; N != i; ++i)
      { // detail::bit_size_v<T> * (i + j) < detail::bit_size_v<T> * N
        std::size_t S(i), j{};

        do
        {
          D const pp(D(nega ? T(~v_[i]) : v_[i]) *
            (negb ? T(~o.v_[j]) : o.v_[j]));

          r += intt(direct2{}, S, T(pp), T(pp >> wbits));
        }
        while (++j, N != ++S);
      }
    }

    //
    if (nega && negb)
    {
      return r + ~*this + ~o + intt(direct{}, T(1));
    }
    else if (nega)
    {
      return -(r + o);
    }
    else if (negb)
    {
      return -(r + *this);
    }
    else
    {
      return r;
    }
  }

  constexpr auto operator/(intt const& o) const noexcept
  {
    return std::get<0>(div(o));
  }

  constexpr auto operator%(intt const& o) const noexcept
  {
    return std::get<1>(div(o));
  }

  //
  /*
  constexpr auto div(intt const& o) const noexcept
  {
    intt<T, 2 * N> r;
    intt q{}; // needed due to clz

    auto const neg(is_neg(*this));

    //
    {
      auto const D(lshifted(is_neg(o) ? -o : o));

      std::size_t CR;

      if (neg)
      {
        auto const tmp(-*this);

        CR = clz(tmp);
        r = {tmp, direct{}};
      }
      else
      {
        CR = clz(*this);
        r = {*this, direct{}};
      }

      r <<= CR;

      for (auto i(N * wbits - CR); i;)
      {
        --i;

        if (unsigned_compare(r <<= 1, D) >= 0)
        {
          r -= D;

          set_bit(q, i);
        }
      }
    }

    //
    auto const tmp(rshifted(r));

    return std::pair(neg ^ is_neg(o) ? -q : q, neg ? -tmp : tmp);
  }
  */

  constexpr auto div(intt const& o) const noexcept
  { // wbits per iteration
    using H = std::conditional_t<
      std::is_same_v<T, std::uint64_t>,
      std::uint32_t,
      std::conditional_t<
        std::is_same_v<T, std::uint16_t>,
        std::uint8_t,
        std::uint8_t
      >
    >;

    auto const nega(is_neg(*this)), negb(is_neg(o));

    intt<T, 2 * N> a{nega ? -*this : *this, direct{}};

    //
    enum : std::size_t { M = 2 * N, hwbits = wbits / 2 };
    enum : H { dmax = (T(1) << hwbits) - 1 };

    intt q;

    {
      std::size_t C;

      intt<T, M> b;

      if (negb)
      {
        auto const tmp(-o);

        b = {tmp, direct{}};
        C = clz(tmp);
      }
      else
      {
        b = {o, direct{}};
        C = clz(o);
      }

      lshl(a, C);
      lshl(b, C);
      wshl(b, N);

      H const B(b.v_[M - 1] >> hwbits);

      std::size_t k(M);

      do
      {
        --k;

        //
        auto h(std::min(H(dmax), H(a.v_[k] / B)));

        for (a -= h * lshr(b, hwbits); is_neg(a); a += b, --h);

        auto l(
          std::min(
            H(dmax),
            H((T(a.v_[k] << hwbits) | T(a.v_[k - 1] >> hwbits)) / B)
          )
        );

        for (a -= l * lshr(b, hwbits); is_neg(a); a += b, --l);

        //
        q.v_[k - N] = T(h) << hwbits | l;
      }
      while (N != k);

      lshr(a, C);
    }

    //
    return std::pair(nega ^ negb ? -q : q, nega ? -intt(a) : intt(a));
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
    auto const nega(is_neg(*this));

    return nega == is_neg(o) ?
      unsigned_compare(*this, o) :
      nega ? std::strong_ordering::less: std::strong_ordering::greater;
  }

  //
  static constexpr auto max() noexcept { return -++min(); }
  static constexpr auto min() noexcept { return intt(1) << N * wbits - 1; }
};

// conversions
#define INTT_LEFT_CONVERSION(OP)\
template <typename A, std::size_t B, typename U>\
constexpr auto operator OP (U&& a, intt<A, B> const& b) noexcept\
  requires(std::is_enum_v<std::remove_cvref_t<U>> ||\
    std::is_integral_v<std::remove_cvref_t<U>>)\
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
    std::is_integral_v<std::remove_cvref_t<U>>)\
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
constexpr auto clz(intt<T, N> const& a) noexcept
{
  decltype(N) n{};

  {
    auto I{N};

    int c;

    do
    {
      n += c = std::countl_zero(a.v_[--I]);
    } while (I && (intt<T, N>::wbits == c));
  }

  return n;
}

template <std::size_t I, typename T, std::size_t N>
constexpr void clear_bit(intt<T, N>& a) noexcept
{
  a.v_[I / intt<T, N>::wbits] &= ~(T{1} << (I % intt<T, N>::wbits));
}

template <typename T, std::size_t N>
constexpr void clear_bit(intt<T, N>& a, std::size_t const i) noexcept
{
  a.v_[i / intt<T, N>::wbits] &= ~(T{1} << i % intt<T, N>::wbits);
}

template <std::size_t I, typename T, std::size_t N>
constexpr void set_bit(intt<T, N>& a) noexcept
{
  a.v_[I / intt<T, N>::wbits] |= T{1} << I % intt<T, N>::wbits;
}

template <typename T, std::size_t N>
constexpr void set_bit(intt<T, N>& a, std::size_t const i) noexcept
{
  a.v_[i / intt<T, N>::wbits] |= T{1} << i % intt<T, N>::wbits;
}

template <std::size_t I, typename T, std::size_t N>
constexpr bool test_bit(intt<T, N> const& a) noexcept
{
  return a.v_[I / intt<T, N>::wbits] & (T{1} << I % intt<T, N>::wbits);
}

template <typename T, std::size_t N>
constexpr auto is_neg(intt<T, N> const& a) noexcept
{
  return test_bit<N * intt<T, N>::wbits - 1>(a);
}

template <typename T, std::size_t N>
constexpr auto& lshl(intt<T, N>& a, std::size_t M) noexcept
{
  if (M)
  {
    auto const shl([&]<auto ...I>(auto const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            a.v_[N - 1 - I] = (a.v_[N - 1 - I] << e) |
              (a.v_[N - 1 - I - 1] >> (intt<T, N>::wbits - e))
          ),
          ...
        );

        *a.v_ <<= e;
      }
    );

    for (; std::size_t(M) >= intt<T, N>::wbits; M -= intt<T, N>::wbits - 1)
    {
      shl.template operator()(
        intt<T, N>::wbits - 1,
        std::make_index_sequence<N - 1>()
      );
    }

    shl.template operator()(M, std::make_index_sequence<N - 1>());
  }

  return a;
}

template <typename T, std::size_t N>
constexpr auto& lshr(intt<T, N>& a, std::size_t M) noexcept
{
  if (M)
  {
    auto const shr([&a]<auto ...I>(auto const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            a.v_[I] = (a.v_[I] >> e) |
              (a.v_[I + 1] << (intt<T, N>::wbits - e))
          ),
          ...
        );

        a.v_[N - 1] >>= e;
      }
    );

    for (; std::size_t(M) >= intt<T, N>::wbits; M -= intt<T, N>::wbits - 1)
    {
      shr.template operator()(
        intt<T, N>::wbits - 1,
        std::make_index_sequence<N - 1>()
      );
    }

    shr.template operator()(M, std::make_index_sequence<N - 1>());
  }

  return a;
}

constexpr auto& wshl(auto& a, std::size_t const n) noexcept
{
  auto i{a.size()};

  if (n && (a.size() > n))
  {
    for (auto j(a.size() - n); j;)
    {
      a.v_[--i] = a.v_[--j];
    }
  }

  while (i) a.v_[--i] = {};

  return a;
}

constexpr auto wshl(auto const& a, std::size_t const n) noexcept
{
  std::remove_cvref_t<decltype(a)> r;

  auto i{a.size()};

  if (n && (a.size() > n))
  {
    for (auto j(a.size() - n); j;)
    {
      r.v_[--i] = a.v_[--j];
    }
  }

  while (i) r.v_[--i] = {};

  return r;
}

constexpr auto& wshr(auto& a, std::size_t const n) noexcept
{
  std::size_t i{};

  if (n)
  {
    for (auto j(n); j < a.size();)
    {
      a.v_[i++] = a.v_[j++];
    }
  }

  for (; a.size() != i; ++i) a.v_[i] = {};

  return a;
}

template <typename T, std::size_t N>
constexpr auto lshifted(intt<T, N> const& a) noexcept
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
            r.v_[I] = a.v_[I - N];
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

template <typename T, std::size_t N>
constexpr auto rshifted(intt<T, N> const& a) noexcept
{
  intt<T, N / 2> r;

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((r.v_[I] = a.v_[N / 2 + I]), ...);
  }(std::make_index_sequence<N / 2>());

  return r;
}

template <typename T, std::size_t N>
constexpr auto unsigned_compare(intt<T, N> const& a,
  intt<T, N> const& b) noexcept
{
  auto i{N};

  do
  {
    --i;

    if (auto const c(a[i] <=> b[i]); c < 0)
    {
      return std::strong_ordering::less;
    }
    else if (c > 0)
    {
      return std::strong_ordering::greater;
    }
  }
  while (i);

  return std::strong_ordering::equal;
}

template <typename T, std::size_t N>
constexpr auto sqrt(intt<T, N> const& a) noexcept
{
  intt<T, 2 * N> r(a);
  intt<T, N> q{};

  //
  {
    auto const CR(clz(a));
    r <<= CR;

    for (auto i(N * intt<T, N>::wbits - CR); i;)
    {
      --i;

      set_bit(q, i);

      if (auto const Q(lshifted(q)); unsigned_compare(r <<= 1, Q) >= 0)
      {
        r -= Q;
      }
      else
      {
        clear_bit(q, i);
      }
    }
  }

  //
  return std::pair(q, rshifted(r));
}

//
template <typename T>
constexpr std::pair<T, bool> to_integral(std::input_iterator auto i,
  decltype(i) const end) noexcept
{
  if (T r{}; i == end)
  {
    return {r, true};
  }
  else
  {
    bool neg{};

    switch (*i)
    {
      case '0': case '1': case '2': case '3': case '4':
      case '5': case '6': case '7': case '8': case '9':
      case '.':
        break;

      case '-':
        neg = true;
        [[fallthrough]];

      case '+':
        i = std::next(i);
        break;

      default:
        return {r, true};
    }

    auto const scandigit([neg, &r, min(T::min()), max(T::max())](
      decltype(r) const d) noexcept
      {
        if (neg)
        {
          if (r >= min / 10)
          {
            if (auto const t(10 * r); t >= min + d)
            {
              r = t - d;

              return false;
            }
          }
        }
        else if (r <= max / 10)
        {
          if (auto const t(10 * r); t <= max - d)
          {
            r = t + d;

            return false;
          }
        }

        return true;
      }
    );

    for (; end != i; i = std::next(i))
    {
      switch (*i)
      {
        case '0': case '1': case '2': case '3': case '4':
        case '5': case '6': case '7': case '8': case '9':
          if (scandigit(*i - '0')) return {r, true}; else continue;

        case '\0':
          break;

        default:
          return {r, true};
      }

      break;
    }

    return {r, false};
  }
}

template <typename T, typename S>
constexpr auto to_integral(S const& s) noexcept ->
  decltype(std::cbegin(s), std::cend(s), std::pair<T, bool>())
{
  return to_integral<T>(std::cbegin(s), std::cend(s));
}

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
  auto const neg(is_neg(a));

  std::string r(neg ? 1 : 0, '-');

  {
    intt<T, N> const k(direct{}, T(10));

    do
    {
      auto const p(a.div(k));

      signed char const d(std::get<1>(p));

      r.insert(neg, 1, '0' + (neg ? -d : d));

      a = std::get<0>(p);
    }
    while (a);
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
