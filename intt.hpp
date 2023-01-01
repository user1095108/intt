#ifndef INTT_HPP
# define INTT_HPP
# pragma once

#include <cassert>
#include <climits> // CHAR_BIT
#include <cmath> // std::ldexp()

#include <concepts> // std::floating_point, std::integral
#include <algorithm> // std::max()
#include <bit> // std::countl_zero
#include <iomanip> // std::hex
#include <iterator>
#include <ostream>
#include <sstream>
#include <utility> // std::pair
#include <type_traits>

namespace intt
{

struct direct{};

enum feat
{
  NAIMUL,
  SEQMUL,
  NAIDIV,
  NEWDIV,
  SEQDIV,
};

template <
  std::unsigned_integral,
  std::size_t N,
  enum feat...
> requires(N > 0) struct intt;

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

template <auto ...F>
consteval auto contains(auto const f) noexcept
{
  return ((f == F) || ...);
}

template <auto C> static constexpr auto coeff() noexcept { return C; }

template <typename> struct is_intt : std::false_type {};

template <typename T, std::size_t N, enum feat... F>
struct is_intt<intt<T, N, F...>> : std::true_type {};

template <typename> struct halve;

template <typename T, std::size_t N, enum feat... F>
struct halve<intt<T, N, F...>> { using type = intt<T, N / 2, F...>; };

}

template <typename T>
concept intt_type = detail::is_intt<std::remove_cvref_t<T>>::value;

template <std::unsigned_integral T, std::size_t N, enum feat... F>
  requires(N > 0)
struct intt
{
  enum : std::size_t
  {
    wbits = sizeof(T) * CHAR_BIT, // bits per word
    words = N
  };

  using value_type = T;

  using doubled_t = intt<T, 2 * N, F...>;

  T v_[N];

  intt() = default;

  intt(intt const&) = default;
  intt(intt&&) = default;

  constexpr intt(direct, auto&& ...a) noexcept:
    v_{std::forward<decltype(a)>(a)...}
  {
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

  template <std::size_t M, enum feat... FF>
  constexpr intt(intt<T, M, FF...> const& o) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      auto const neg(is_neg(o));

      (
        (v_[I] = I < M ? o.v_[I] : neg ? ~T{} : T{}),
        ...
      );
    }(std::make_index_sequence<N>());
  }

  template <std::size_t M, enum feat... FF>
  constexpr intt(intt<T, M, FF...> const& o, direct) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      (
        (v_[I] = I < M ? o.v_[I] : T{}),
        ...
      );
    }(std::make_index_sequence<N>());
  }

  template <typename U, std::size_t M, enum feat... FF>
  constexpr intt(intt<U, M, FF...> const& o) noexcept
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
  constexpr explicit operator U() const noexcept
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
    add_words<0>(*this, T(1)); return *this;
  }

  constexpr auto& operator--() noexcept
  {
    sub_words<0>(*this, T(1)); return *this;
  }

  constexpr auto operator++(int) noexcept
  {
    auto const r(*this); ++*this; return r;
  }

  constexpr auto operator--(int) noexcept
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
      auto& s(r.v_);

      ((s[I] = T(~s[I])), ...);

      bool c{true};

      ((c = (s[I] += c) < c), ...);
    }(std::make_index_sequence<N>());

    return r;
  }

  //
  constexpr auto operator+(intt const& o) const noexcept
  {
    intt r;

    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      bool c;

      (
        [&]() noexcept
        {
          auto& s(r.v_[I]);
          auto const& a(v_[I]);

          if constexpr(I)
          {
            s = c + a + o.v_[I];
            c = c ? s <= a : s < a;
          }
          else
          {
            c = (s = a + o.v_[I]) < a;
          }
        }(),
        ...
      );
    }(std::make_index_sequence<N>());

    return r;
  }

  constexpr auto operator-(intt const& o) const noexcept
  {
    intt r;

    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      bool c;

      (
        [&]() noexcept
        {
          auto& d(r.v_[I]);
          auto const& a(v_[I]);

          if constexpr(I)
          {
            d = a - o.v_[I] - c;
            c = c ? d >= a : d > a;
          }
          else
          {
            c = (d = a - o.v_[I]) > a;
          }
        }(),
        ...
      );
    }(std::make_index_sequence<N>());

    return r;
  }

  constexpr auto operator*(intt const& o) const noexcept
  {
    if constexpr(detail::contains<F...>(NAIMUL))
    {
      return naimul(o);
    }
    else if constexpr(detail::contains<F...>(SEQMUL))
    {
      return seqmul(o);
    }
    else
    {
      return naimul(o);
    }
  }

  constexpr auto operator/(intt const& o) const noexcept
  {
    if constexpr(detail::contains<F...>(NAIDIV))
    {
      return naidiv<false>(o);
    }
    else if constexpr(detail::contains<F...>(NEWDIV))
    {
      return newdiv<false>(o);
    }
    else if constexpr(detail::contains<F...>(SEQDIV))
    {
      return seqdiv<false>(o);
    }
    else
    {
      return naidiv<false>(o);
    }
  }

  constexpr auto operator%(intt const& o) const noexcept
  {
    if constexpr(detail::contains<F...>(NAIDIV))
    {
      return naidiv<true>(o);
    }
    else if constexpr(detail::contains<F...>(NEWDIV))
    {
      return newdiv<true>(o);
    }
    else if constexpr(detail::contains<F...>(SEQDIV))
    {
      return seqdiv<true>(o);
    }
    else
    {
      return naidiv<true>(o);
    }
  }

  //
  constexpr auto naimul(intt const& o) const noexcept
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

      enum : std::size_t { M = 2 * N, hwbits = wbits / 2 };

      for (std::size_t i{}; M != i; ++i)
      { // detail::bit_size_v<H> * (i + j) < wbits * N
        auto S(i);

        do
        {
          T pp;

          {
            H const a(v_[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0));
            auto const j(S - i);
            H const b(o.v_[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0));
            pp = T(nega ? H(~a) : a) * (negb ? H(~b) : b);
          }

          S % 2 ?
            add_words(r, S / 2, pp << hwbits, pp >> hwbits) :
            add_words(r, S / 2, pp);
        }
        while (M != ++S);
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
        auto S(i);

        do
        {
          D const pp(D(nega ? T(~v_[i]) : v_[i]) *
            (negb ? T(~o.v_[S - i]) : o.v_[S - i]));

          add_words(r, S, T(pp), T(pp >> wbits));
        }
        while (N != ++S);
      }
    }

    //
    if (nega && negb)
    {
      //return r + ~(*this + o) + intt(direct{}, T(1));
      return r - *this - o;
    }
    else if (nega)
    {
      return -r - o;
    }
    else if (negb)
    {
      return -r - *this;
    }
    else
    {
      return r;
    }
  }

  constexpr auto seqmul(intt const& o) const noexcept
  {
    // A is lshifted, so r needs to be as well
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

          lshr<1>(r);
        }(),
        ...
      );
    }(std::make_index_sequence<wbits * N - 1>());

    if (is_neg(o))
    {
      r -= A;
    }

    return intt(lshr<1>(r), direct{});
  }

  //
  template <bool Rem = false>
  constexpr auto naidiv(intt const& o) const noexcept
  { // wbits per iteration
    using H = std::conditional_t<
      std::is_same_v<T, std::uint64_t>,
      std::uint32_t,
      std::conditional_t<
        std::is_same_v<T, std::uint32_t>,
        std::uint16_t,
        std::uint8_t
      >
    >;

    enum : std::size_t { M = 2 * N, hwbits = wbits / 2 };
    enum : H { dmax = (T(1) << hwbits) - 1 };

    auto const nega(is_neg(*this)), negb(is_neg(o));

    intt<T, M, F...> a{nega ? -*this : *this, direct{}};

    intt q;

    //
    std::size_t C;

    {
      intt<T, M, F...> b;

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
      wshl<N>(b);

      H const B(b.v_[M - 1] >> hwbits);

      std::size_t k(M);

      do
      {
        --k;

        auto h(std::min(H(dmax), H(a.v_[k] / B)));

        for (a -= hwmul(h, hwlshr(b)); is_neg(a); a += b, --h);

        auto l(
          std::min(
            H(dmax),
            H((T(a.v_[k] << hwbits) | T(a.v_[k - 1] >> hwbits)) / B)
          )
        );

        for (a -= hwmul(l, hwlshr(b)); is_neg(a); a += b, --l);

        //
        q.v_[k - N] = T(h) << hwbits | l;
      }
      while (N != k);
    }

    //
    if constexpr(Rem)
    {
      lshr(a, C);

      return nega ? -intt(a, direct{}) : intt(a, direct{});
    }
    else
    {
      return nega == negb ? q : -q;
    }
  }

  template <bool Rem = false>
  constexpr auto newdiv(intt const& o) const noexcept
  {
    enum : std::size_t { M = 2 * N };

    auto const nega(is_neg(*this)), negb(is_neg(o));

    intt q;

    {
      constexpr auto make_coeff([](int const a, int const b) noexcept
        {
          return wshl<N>(intt<T, 2 * N, F...>(a)).seqdiv(b);
        }
      );

      std::size_t C;

      intt<T, M, F...> b;

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

      lshl(b, C);

      auto const k(detail::coeff<wshl<N>(intt<T, M, F...>(direct{}, T(2)))>());

      //auto xn(detail::coeff<wshl<N>(intt<T, M, F...>(direct{}, T(2)))>() - b);

      auto xn(
        detail::coeff<make_coeff(48, 17)>() -
        unewmul<N>(b, detail::coeff<make_coeff(32, 17)>())
      );

      // x_n = x_n(2 - a*x_n)
      for (intt<T, M, F...> tmp; tmp = unewmul<N>(b, xn), tmp.v_[N - 1];)
      {
        xn = newmul<N>(xn, k - tmp);
      }

      q = lshr(
          unewmul<N>(
            intt<T, M, F...>{nega ? -*this : *this, direct{}},
            xn
          ),
          N * wbits - C
        );
    }

    //
    if constexpr(Rem)
    {
      auto const r{
        intt{nega ? -*this : *this} -
        umul(q, intt{negb ? -o : o})
      };

      return nega ? -r : r;
    }
    else
    {
      return nega == negb ? q : -q;
    }
  }

  template <bool Rem = false>
  constexpr auto seqdiv(intt const& o) const noexcept
  {
    intt<T, 2 * N, F...> r;
    intt q{}; // needed due to clz

    auto const nega(is_neg(*this)), negb(is_neg(o));

    //
    {
      auto const D(lshifted(negb ? -o : o));

      std::size_t CR;

      if (nega)
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

      lshl(r, CR);

      for (auto i(N * wbits - CR); i;)
      {
        --i;

        if (ucompare(lshl<1>(r), D) >= 0)
        {
          r -= D;

          set_bit(q, i);
        }
      }
    }

    //
    if constexpr(Rem)
    {
      auto const tmp(rshifted(r));

      return nega ? -tmp : tmp;
    }
    else
    {
      return nega == negb ? q : -q;
    }
  }

  //
  constexpr bool operator==(intt const& o) const noexcept
  {
    return [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        return ((v_[N - 1 - I] == o.v_[N - 1 - I]) && ...);
      }(std::make_index_sequence<N>());
  }

  constexpr auto operator<=>(intt const& o) const noexcept
  {
    auto const c(is_neg(o) <=> is_neg(*this));

    return c == 0 ? ucompare(*this, o) : c;
  }

  //
  static constexpr auto max() noexcept
  {
    return detail::coeff<-++min()>();
  }

  static constexpr auto min() noexcept
  {
    return detail::coeff<intt(1) << N * wbits - 1>();
  }
};

// conversions
#define INTT_LEFT_CONVERSION(OP)\
template <typename A, std::size_t B, enum feat... F, typename U>\
constexpr auto operator OP (U&& a, intt<A, B, F...> const& b) noexcept\
  requires(std::is_enum_v<std::remove_cvref_t<U>> ||\
    std::is_integral_v<std::remove_cvref_t<U>>)\
{\
  return intt<A, B, F...>(std::forward<U>(a)) OP b;\
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
template <typename A, std::size_t B, enum feat...F, typename U>\
constexpr auto operator OP (intt<A, B, F...> const& a, U&& b) noexcept\
  requires(std::is_enum_v<std::remove_cvref_t<U>> ||\
    std::is_integral_v<std::remove_cvref_t<U>>)\
{\
  return a OP intt<A, B, F...>(std::forward<U>(b));\
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

//utilities///////////////////////////////////////////////////////////////////
constexpr bool is_neg(intt_type auto const& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using S = std::make_signed_t<typename U::value_type>;

  return S(a.v_[U::words - 1]) < S{};
}

constexpr auto clz(intt_type auto const& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;

  enum : std::size_t { N = U::words };

  detail::underlying_type_t<decltype(N)> r{};

  {
    decltype(r) I{N};

    int c;

    do
    {
      r += c = std::countl_zero(a.v_[--I]);
    } while (I && (U::wbits == c));
  }

  return r;
}

template <std::size_t I>
constexpr void clear_bit(intt_type auto& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;
  a.v_[I / U::wbits] &= ~(T{1} << I % U::wbits);
}

constexpr void clear_bit(intt_type auto& a, std::size_t const i) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;
  a.v_[i / U::wbits] &= ~(T{1} << i % U::wbits);
}

template <std::size_t I>
constexpr void set_bit(intt_type auto& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;
  a.v_[I / U::wbits] |= T{1} << I % U::wbits;
}

constexpr void set_bit(intt_type auto& a, std::size_t const i) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;
  a.v_[i / U::wbits] |= T{1} << i % U::wbits;
}

template <std::size_t I>
constexpr bool test_bit(intt_type auto const& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;
  return a.v_[I / U::wbits] & T{1} << I % U::wbits;
}

template <std::size_t M>
constexpr auto& lshl(intt_type auto&& a) noexcept requires(bool(M))
{
  using U = std::remove_cvref_t<decltype(a)>;

  enum : std::size_t {N = U::words};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (
        a.v_[N - 1 - I] = (a.v_[N - 1 - I] << M) |
          (a.v_[N - 1 - I - 1] >> (U::wbits - M))
      ),
      ...
    );

    *a.v_ <<= M;
  }(std::make_index_sequence<N - 1>());

  return a;
}

constexpr auto& lshl(intt_type auto&& a, std::size_t M) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;

  enum : std::size_t {N = U::words};

  if (M)
  {
    auto const shl([&]<auto ...I>(auto const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            a.v_[N - 1 - I] = (a.v_[N - 1 - I] << e) |
              (a.v_[N - 1 - I - 1] >> (U::wbits - e))
          ),
          ...
        );

        *a.v_ <<= e;
      }
    );

    for (; std::size_t(M) >= U::wbits; M -= U::wbits - 1)
    {
      shl.template operator()(
        U::wbits - 1,
        std::make_index_sequence<N - 1>()
      );
    }

    shl.template operator()(M, std::make_index_sequence<N - 1>());
  }

  return a;
}

template <std::size_t M>
constexpr auto& lshr(intt_type auto&& a) noexcept requires(bool(M))
{
  using U = std::remove_cvref_t<decltype(a)>;

  enum : std::size_t {N = U::words};

  [&a]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (
        a.v_[I] = (a.v_[I + 1] << (U::wbits - M)) | (a.v_[I] >> M)
      ),
      ...
    );

    a.v_[N - 1] >>= M;
  }(std::make_index_sequence<N - 1>());

  return a;
}

constexpr auto& lshr(intt_type auto&& a, std::size_t M) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;

  enum : std::size_t {N = U::words};

  if (M)
  {
    auto const shr([&a]<auto ...I>(auto const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            a.v_[I] = (a.v_[I + 1] << (U::wbits - e)) | (a.v_[I] >> e)
          ),
          ...
        );

        a.v_[N - 1] >>= e;
      }
    );

    for (; std::size_t(M) >= U::wbits; M -= U::wbits - 1)
    {
      shr.template operator()(
        U::wbits - 1,
        std::make_index_sequence<N - 1>()
      );
    }

    shr.template operator()(M, std::make_index_sequence<N - 1>());
  }

  return a;
}

constexpr auto& hwlshr(intt_type auto&& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t {N = U::words, hwbits = U::wbits / 2};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (
        a.v_[I] = T(a.v_[I] >> hwbits) | T(a.v_[I + 1] << hwbits)
      ),
      ...
    );
  }(std::make_index_sequence<N - 1>());

  a.v_[N - 1] >>= hwbits;

  return a;
}

template <std::size_t M>
constexpr auto& wshl(intt_type auto&& a) noexcept requires(bool(M))
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t {N = U::words};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (a.v_[N - 1 - I] = M + I < N ? a.v_[N - 1 - M - I] : T{}),
      ...
    );
  }(std::make_index_sequence<N>());

  return a;
}

template <std::size_t M>
constexpr auto& wshr(intt_type auto&& a) noexcept requires(bool(M))
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t {N = U::words};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (a.v_[I] = M + I < N ? a.v_[I + M] : T{}),
      ...
    );
  }(std::make_index_sequence<N>());

  return a;
}

constexpr auto lshifted(intt_type auto const& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  typename U::doubled_t r;

  enum : std::size_t {M = decltype(r)::words, N = U::words};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (r.v_[I] = I >= N ? a.v_[I - N] : T{}),
      ...
    );
  }(std::make_index_sequence<M>());

  return r;
}

constexpr auto rshifted(intt_type auto const& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;

  typename detail::halve<U>::type r;

  enum : std::size_t {M = decltype(r)::words};

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((r.v_[I] = a.v_[M + I]), ...);
  }(std::make_index_sequence<M>());

  return r;
}

constexpr auto hwmul(auto const k, intt_type auto const& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t
  {
    M = 2 * U::words,
    N = U::words,
    wbits = U::wbits,
    hwbits = wbits / 2
  };

  U r{};

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

    [&]<auto ...S>(std::index_sequence<S...>) noexcept
    {
      (
        [&]() noexcept
        {
          T const pp(
            T(H(k)) * H(a.v_[S / 2] >> (S % 2 ? std::size_t(hwbits) : 0))
          );

          if constexpr((S % 2) && (M - 1 == S))
          {
            add_words<S / 2>(r, pp << hwbits);
          }
          else if constexpr(S % 2)
          {
            add_words<S / 2>(r, pp << hwbits, pp >> hwbits);
          }
          else
          {
            add_words<S / 2>(r, pp);
          }
        }(),
        ...
      );
    }(std::make_index_sequence<M>());
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

    [&]<auto ...S>(std::index_sequence<S...>) noexcept
    {
      (
        [&]() noexcept
        {
          D const pp(D(k) * a.v_[S]);

          if constexpr(N - 1 == S)
          {
            add_words<S>(r, T(pp));
          }
          else
          {
            add_words<S>(r, T(pp), T(pp >> wbits));
          }
        }(),
        ...
      );
    }(std::make_index_sequence<N>());
  }

  //
  return r;
}

template <std::size_t O>
constexpr auto newmul(intt_type auto const& a, decltype(a) b) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t { N = U::words };

  auto const nega(is_neg(a)), negb(is_neg(b));

  U r{};

  if constexpr(std::is_same_v<T, std::uint64_t>)
  {
    using H = std::conditional_t<
      std::is_same_v<T, std::uint64_t>,
      std::uint32_t,
      std::conditional_t<
        std::is_same_v<T, std::uint16_t>,
        std::uint8_t,
        std::uint8_t
      >
    >;

    enum : std::size_t { M = 2 * O, hwbits = U::wbits / 2 };

    for (std::size_t i{}; M != i; ++i)
    {
      for (std::size_t j{}; M != j; ++j)
      {
        T pp;

        {
          H const ai(a.v_[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0));
          H const bj(b.v_[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0));
          pp = T(nega ? H(~ai) : ai) * (negb ? H(~bj) : bj);
        }

        auto const S(i + j);

        S % 2 ?
          add_words(r, S / 2, pp << hwbits, pp >> hwbits) :
          add_words(r, S / 2, pp);
      }
    }
  }
  else
  {
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

    for (std::size_t i{}; O != i; ++i)
    {
      for (std::size_t j{}; O != j; ++j)
      {
        D const pp(D(nega ? T(~a.v_[i]) : a.v_[i]) *
          (negb ? T(~b.v_[j]) : b.v_[j]));

        add_words(r, i + j, T(pp), T(pp >> U::wbits));
      }
    }
  }

  //
  wshr<O>(r);

  {
    auto A{nega ? -a.v_[O] : a.v_[O]};
    auto B{negb ? -b.v_[O] : b.v_[O]};

    r.v_[O] = A * B;

    {
      auto const bb(
        negb ? -intt<T, O>(b, direct{}) : intt<T, O>(b, direct{})
      );

      while (A) --A, r += bb;
    }

    {
      auto const aa(
        nega ? -intt<T, O>(a, direct{}) : intt<T, O>(a, direct{})
      );

      while (B) --B, r += aa;
    }
  }

  //
  if (nega && negb)
  {
    return r - a - b;
  }
  else if (nega)
  {
    return -r - b;
  }
  else if (negb)
  {
    return -r - a;
  }
  else
  {
    return r;
  }
}

template <std::size_t O>
constexpr auto unewmul(intt_type auto const& a, decltype(a) b) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t { N = U::words };

  auto const nega(is_neg(a)), negb(is_neg(b));

  U r{};

  if constexpr(std::is_same_v<T, std::uint64_t>)
  {
    using H = std::conditional_t<
      std::is_same_v<T, std::uint64_t>,
      std::uint32_t,
      std::conditional_t<
        std::is_same_v<T, std::uint16_t>,
        std::uint8_t,
        std::uint8_t
      >
    >;

    enum : std::size_t { M = 2 * O, hwbits = U::wbits / 2 };

    for (std::size_t i{}; M != i; ++i)
    {
      for (std::size_t j{}; M != j; ++j)
      {
        T pp;

        {
          H const ai(a.v_[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0));
          H const bj(b.v_[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0));
          pp = T(nega ? H(~ai) : ai) * (negb ? H(~bj) : bj);
        }

        auto const S(i + j);

        S % 2 ?
          add_words(r, S / 2, pp << hwbits, pp >> hwbits) :
          add_words(r, S / 2, pp);
      }
    }
  }
  else
  {
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

    for (std::size_t i{}; O != i; ++i)
    {
      for (std::size_t j{}; O != j; ++j)
      {
        D const pp(D(nega ? T(~a.v_[i]) : a.v_[i]) *
          (negb ? T(~b.v_[j]) : b.v_[j]));

        add_words(r, i + j, T(pp), T(pp >> U::wbits));
      }
    }
  }

  //
  wshr<O>(r);

  {
    auto A{nega ? -a.v_[O] : a.v_[O]};
    auto B{negb ? -b.v_[O] : b.v_[O]};

    r.v_[O] = A * B;

    {
      auto const bb(
        negb ? -intt<T, O>(b, direct{}) : intt<T, O>(b, direct{})
      );

      while (A) --A, r += bb;
    }

    {
      auto const aa(
        nega ? -intt<T, O>(a, direct{}) : intt<T, O>(a, direct{})
      );

      while (B) --B, r += aa;
    }
  }

  //
  return r;
}

constexpr auto ucompare(intt_type auto const& a, decltype(a) b) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;

  {
    detail::underlying_type_t<decltype(U::words)> i{U::words};

    do
    {
      --i;

      if (auto const c(a[i] <=> b[i]); c != 0)
      {
        return c;
      }
    }
    while (i);
  }

  return std::strong_ordering::equal;
}

constexpr auto umul(intt_type auto const& a, decltype(a) b) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t
  {
    M = 2 * U::words,
    N = U::words,
    wbits = U::wbits,
    hwbits = wbits / 2
  };

  U r{};

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

    for (std::size_t i{}; M != i; ++i)
    { // detail::bit_size_v<H> * (i + j) < wbits * N
      auto S(i);

      do
      {
        T pp;

        {
          auto const j(S - i);

          pp = T(H(a.v_[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0))) *
            H(b.v_[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0));
        }

        S % 2 ?
          add_words(r, S / 2, pp << hwbits, pp >> hwbits) :
          add_words(r, S / 2, pp);
      }
      while (M != ++S);
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
      auto S(i);

      do
      {
        D const pp(D(a.v_[i]) * b.v_[S - i]);

        add_words(r, S, T(pp), T(pp >> wbits));
      }
      while (N != ++S);
    }
  }

  //
  return r;
}

template <std::size_t, typename T>
constexpr auto get_word() noexcept
{
  return T{};
}

template <std::size_t I, typename T>
constexpr decltype(auto) get_word(auto&& a, auto&& ...b) noexcept
{
  if constexpr(I)
  {
    return get_word<I - 1, T>(std::forward<decltype(b)>(b)...);
  }
  else
  {
    return a;
  }
}

template <std::size_t S>
constexpr void add_words(intt_type auto& a, auto&& ...v) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t { N = U::words };

  static_assert(S < N);

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
#ifndef __clang__
    (v, ...);
#endif // __clang__
    bool c{};

    (
      [&]() noexcept
      {
        constexpr auto J(I + S);

        if constexpr(auto& s(a.v_[J]); J - S < sizeof...(v))
        {
          auto const b(get_word<J - S, T>(v...));

          s += c + b;
          c = c ? s <= b : s < b;
        }
        else
        {
          c = (s += c) < c;
        }
      }(),
      ...
    );
  }(std::make_index_sequence<N - S>());
}

template <std::size_t S>
constexpr void sub_words(intt_type auto& a, auto&& ...v) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t { N = U::words };

  static_assert(S < N);

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
#ifndef __clang__
    (v, ...);
#endif // __clang__
    bool c{};

    (
      [&]() noexcept
      {
        constexpr auto J(I + S);

        if constexpr(auto& d(a.v_[J]); J - S < sizeof...(v))
        {
          auto const a(d);
          auto const b(get_word<J - S, T>(v...));

          d = d - b - c;
          c = c ? d >= a : d > a;
        }
        else
        {
          auto const a(d);
          c = (d -= c) > a;
        }
      }(),
      ...
    );
  }(std::make_index_sequence<N - S>());
}

template <typename T>
constexpr auto get_word(std::size_t) noexcept
{
  return T{};
}

template <typename T>
constexpr decltype(auto) get_word(std::size_t const i, auto&& a,
  auto&& ...b) noexcept
{
  return i ?
    get_word<T>(i - 1, std::forward<decltype(b)>(b)...) :
    std::forward<decltype(a)>(a);
}

constexpr void add_words(intt_type auto& a, std::size_t const I,
  auto&& ...v) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t { N = U::words };

  bool c{};

  for (auto i{I}; i != N; ++i)
  {
    auto const b(get_word<T>(i - I, v...));

    auto& s(a.v_[i]);

    s += c + b;
    c = c ? s <= b : s < b;
  }
}

constexpr auto seqsqrt(intt_type auto const& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;

  enum : std::size_t { N = U::words, wbits = U::wbits };

  typename U::doubled_t r(a, direct{}), Q{};

  //
  auto const CR(clz(a));
  lshl(r, CR);

  for (auto i(N * wbits - CR); i;)
  {
    --i;

    if (auto tmp(Q << 1); set_bit(tmp, N * wbits + i),
      ucompare(lshl<1>(r), tmp) >= 0)
    {
      r -= tmp;

      set_bit(Q, N * wbits + i);
    }
  }

  //
  return rshifted(Q);
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

template <typename T>
constexpr auto to_integral(auto const& s) noexcept ->
  decltype(std::cbegin(s), std::cend(s), std::pair<T, bool>())
{
  return to_integral<T>(std::cbegin(s), std::cend(s));
}

template <std::size_t M, typename T, std::size_t N, enum feat... FF>
constexpr auto to_double(intt<T, N, FF...> const& a) noexcept
{
  using F = double;
  using U = std::remove_cvref_t<decltype(a)>;

  if (is_neg(a))
  {
    return [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        return -(((T(~a.v_[I]) *
          std::ldexp(F(1), (int(I) - int(M)) * int(U::wbits))) + ...) +
          std::ldexp(F(1), -int(M) * int(U::wbits)));
      }(std::make_index_sequence<N>());
  }
  else
  {
    return [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        return ((a.v_[I] *
          std::ldexp(F(1), (int(I) - int(M)) * int(U::wbits))) + ...);
      }(std::make_index_sequence<N>());
  }
}

auto to_raw(intt_type auto const& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  enum : std::size_t { N = U::words };

  using V = std::conditional_t<std::is_same_v<T, std::uint8_t>, unsigned, T>;

  std::stringstream ss;

  ss << '"' << std::hex << std::setfill('0');

  for (auto i(N - 1); i; --i)
  {
    ss << std::setw(2) << V(a[i]) << " ";
  }

  ss << std::setw(2) << V(a[0]) << '"';

  return ss.str();
}

std::string to_string(intt_type auto a)
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  auto const neg(is_neg(a));

  std::string r(neg ? 1 : 0, '-');

  {
    U const k(direct{}, T(10));

    do
    {
      std::pair const p(a / k, a % k);

      signed char const d(std::get<1>(p));

      r.insert(neg, 1, '0' + (neg ? -d : d));

      a = std::get<0>(p);
    }
    while (a);
  }

  return r;
}

template <typename T, std::size_t N, enum feat... F>
inline auto& operator<<(std::ostream& os, intt<T, N, F...> const& a)
{
  return os << to_string(a);
}

}

namespace std
{

template <typename T, std::size_t N, enum intt::feat... F>
struct hash<intt::intt<T, N, F...>>
{
  auto operator()(intt::intt<T, N, F...> const& a) const noexcept
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
