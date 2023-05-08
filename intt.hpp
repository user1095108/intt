#ifndef INTT_HPP
# define INTT_HPP
# pragma once

#include <cmath> // std::ldexp()
#include <algorithm> // std::max()
#include <array> // std::to_array()
#include <bit> // std::countl_zero
#include <concepts> // std::floating_point, std::integral
#include <functional> // std::hash
#include <iterator> // std::begin(), std::end()
#include <ostream>
#include <type_traits>

#include "magic.hpp"

namespace intt
{

struct direct{};

enum feat
{
  NAIMUL,
  SEQMUL,
  GLDDIV,
  NAIDIV,
  NEWDIV,
  SEQDIV,
};

template <
  std::unsigned_integral,
  std::size_t N,
  enum feat...
> requires(N > 0) struct intt;

template <typename> struct is_intt : std::false_type {};

template <typename T, std::size_t N, enum feat ...F>
struct is_intt<intt<T, N, F...>> : std::true_type {};

template <typename T>
static constexpr auto is_intt_v{is_intt<T>::value};

template <typename T>
concept intt_concept = is_intt<std::remove_cvref_t<T>>::value;

template <auto C> static constexpr auto coeff() noexcept { return C; }

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

template <typename> struct double_ { using type = void; };

template <typename T, std::size_t N, enum feat ...F>
struct double_<intt<T, N, F...>> { using type = intt<T, 2 * N, F...>; };

template <typename T> using double_t = typename double_<T>::type;

template <auto ...F>
consteval auto contains([[maybe_unused]] auto const f) noexcept
{
  return ((f == F) || ...);
}

consteval std::size_t num_digits(std::size_t const N) noexcept
{
  return N / 3 + bool(N % 3); // 2^N <= 8^J, J >= N * log8(2) = N / 3
}

}

template <std::unsigned_integral T, std::size_t N, enum feat... F>
  requires(N > 0)
struct intt
{
  enum : std::size_t
  {
    wbits = sizeof(T) * CHAR_BIT, // bits per word
    words = N,
    bits = wbits * words
  };

  using value_type = T;

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

  using H = std::conditional_t<
    std::is_same_v<T, std::uint64_t>,
    std::uint32_t,
    std::conditional_t<
      std::is_same_v<T, std::uint32_t>,
      std::uint16_t,
      std::uint8_t
    >
  >;

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

  #define INTT_ASSIGNMENT__(OP)\
    template <typename U>\
    constexpr auto& operator OP ## =(U&& a) noexcept\
    {\
      return *this = *this OP std::forward<U>(a);\
    }

  INTT_ASSIGNMENT__(&)
  INTT_ASSIGNMENT__(|)
  INTT_ASSIGNMENT__(^)
  INTT_ASSIGNMENT__(*)
  INTT_ASSIGNMENT__(/)
  INTT_ASSIGNMENT__(%)

  constexpr auto& operator<<=(std::integral auto const i) noexcept
  {
    return *this = *this << i;
  }

  constexpr auto& operator>>=(std::integral auto const i) noexcept
  {
    return *this = *this >> i;
  }

  constexpr auto& operator+=(intt const& o) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      bool c;

      (
        [&]() noexcept
        {
          auto const& b(o.v_[I]);
          auto& s(v_[I]);

          if constexpr(I)
          {
            s += c + b;
            c = c ? s <= b : s < b;
          }
          else
          {
            c = (s += b) < b;
          }
        }(),
        ...
      );
    }(std::make_index_sequence<N>());

    return *this;
  }

  constexpr auto& operator-=(intt const& o) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      bool c;

      (
        [&]() noexcept
        {
          auto& d(v_[I]);
          auto const a(d);

          if constexpr(I)
          {
            d = a - o.v_[I] - c;
            c = c ? d >= a : d > a;
          }
          else
          {
            c = (d -= o.v_[I]) > a;
          }
        }(),
        ...
      );
    }(std::make_index_sequence<N>());

    return *this;
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
    return is_neg(*this) ?
      [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        return -((U{1} + ... + (T(~v_[I]) * std::ldexp(U(1), I * wbits))));
      }(std::make_index_sequence<N>()) :
      [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        return ((v_[I] * std::ldexp(U(1), I * wbits)) + ...);
      }(std::make_index_sequence<N>());
  }

  template <std::integral U>
  constexpr operator U() const noexcept
  {
    return [&]<auto ...I>(std::index_sequence<I...>) noexcept
      {
        if constexpr(bool(sizeof...(I)))
        { // words shifted to the left
          if constexpr(detail::bit_size_v<U> > N * wbits)
          {
            return is_neg(*this) ?
              (((I < N ? U(v_[I]) : U(~U{})) << I * wbits) | ...) :
              (((I < N ? U(v_[I]) : U{}) << I * wbits) | ...);
          }
          else
          {
            return ((U(v_[I]) << I * wbits) | ...);
          }
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

  #define INTT_BITWISE__(OP)\
  constexpr auto operator OP(intt const& o) const noexcept\
  {\
    return ([&]<auto ...I>(std::index_sequence<I...>) noexcept -> intt\
      {\
        return {direct{}, T(v_[I] OP o.v_[I])...};\
      }\
    )(std::make_index_sequence<N>());\
  }

  INTT_BITWISE__(&)
  INTT_BITWISE__(|)
  INTT_BITWISE__(^)

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
        shl(wbits - 1, std::make_index_sequence<N - 1>());
      }

      shl(M, std::make_index_sequence<N - 1>());
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
        shr(wbits - 1, std::make_index_sequence<N - 1>());
      }

      shr(M, std::make_index_sequence<N - 1>());
    }

    return r;
  }

  // increment, decrement
  constexpr auto& operator++() noexcept
  {
    add_words<0>(*this, {T(1)}); return *this;
  }

  constexpr auto& operator--() noexcept
  {
    sub_words<0>(*this, {T(1)}); return *this;
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
    intt r;

    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      auto& s(r.v_);
      auto const& a(v_);

      bool c{true};

      ((c = (s[I] = c + T(~a[I])) < c), ...);
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
    if constexpr(detail::contains<F...>(SEQMUL))
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
    if constexpr(detail::contains<F...>(GLDDIV))
    {
      return glddiv<false>(o);
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
    if constexpr(detail::contains<F...>(GLDDIV))
    {
      return glddiv<true>(o);
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
    intt r{};

    if constexpr(std::is_same_v<T, std::uintmax_t>)
    { // multiplying half-words, wbits per iteration
      enum : std::size_t { M = 2 * N, hwbits = wbits / 2 };

      for (std::size_t i{}; M != i; ++i)
      { // detail::bit_size_v<H> * (i + j) < wbits * N
        auto S(i);

        do
        {
          T pp;

          {
            auto const j(S - i);

            pp = T(H(v_[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0))) *
              H(o.v_[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0));
          }

          S % 2 ?
            add_words(r, S / 2, {pp << hwbits, pp >> hwbits}) :
            add_words(r, S / 2, {pp});
        }
        while (M != ++S);
      }
    }
    else
    { // multiplying words, 2 * wbits per iteration
      for (std::size_t i{}; N != i; ++i)
      { // detail::bit_size_v<T> * (i + j) < detail::bit_size_v<T> * N
        auto S(i);

        do
        {
          D const pp(D(v_[i]) * o.v_[S - i]);

          add_words(r, S, {T(pp), T(pp >> wbits)});
        }
        while (N != ++S);
      }
    }

    //
    return r;
  }

  constexpr auto seqmul(intt const& o) const noexcept
  {
    intt<T, 2 * N> r{}, A{*this, direct{}};
    wshl<N>(A);

    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      (
        [&]() noexcept
        {
          if (test_bit<I>(o)) r += A;

          lshr<1>(r);
        }(),
        ...
      );
    }(std::make_index_sequence<wbits * N>());

    return intt(r, direct{});
  }

  //
  template <bool Rem = false>
  constexpr auto glddiv(intt const& o) const noexcept
  {
    enum : std::size_t { M = 2 * N };

    auto const nega(is_neg(*this)), negb(is_neg(o));

    intt q;

    {
      intt<T, M, F...> a{nega ? -*this : *this, direct{}};
      intt<T, M, F...> b;

      std::size_t C;

      {
        auto const tmp(negb ? -o : o);

        C = clz(tmp);
        b = {tmp, direct{}};
      }

      lshl(b, C);

      {
        auto const k(coeff<wshl<N>(intt<T, M, F...>(direct{}, T(2)))>());

        for (auto const end(coeff<wshr<N>(~intt<T, M, F...>{})>()); end != b;)
        {
          auto const l(k - b);

          b = newmul<N>(b, l);
          a = newmul<N>(a, l);
        }
      }

      q = lshr(a, N * wbits - C);
    }

    //
    auto const b(negb ? -o : o);

    if constexpr(auto r((nega ? -*this : *this) - q * b); Rem)
    {
      if (ucompare(r, b) >= 0) r -= b;

      return nega ? -r : r;
    }
    else
    {
      if (ucompare(r, b) >= 0) ++q;

      return nega == negb ? q : -q;
    }
  }

  template <bool Rem = false>
  constexpr auto naidiv(intt const& o) const noexcept
  { // wbits per iteration
    enum : std::size_t { M = 2 * N, hwbits = wbits / 2 };
    enum : T { dmax = (T(1) << hwbits) - 1 };

    auto const nega(is_neg(*this)), negb(is_neg(o));
    intt q{};

    std::size_t CB;
    intt<T, M, F...> a;

    //
    {
      std::size_t CA;

      {
        auto const tmp(nega ? -*this : *this);

        CA = clz(tmp);
        a = {tmp, direct{}};
      }

      intt<T, M, F...> b;

      {
        auto const tmp(negb ? -o : o);

        CB = clz(tmp);
        b = {tmp, direct{}};
      }

      lshl(a, CB);

      if (CB >= CA) [[likely]]
      {
        wshl<N>(lshl(b, CB));

        H const B(b.v_[M - 1] >> hwbits);

        auto k(N + (CB - CA) / wbits + 1);
        wshr(b, M - k);

        do
        {
          --k;

          //
          T h(a.v_[k] / B);
          if (h >> hwbits) [[unlikely]] h = dmax;

          for (a -= hwmul(lshr<hwbits>(b), h); is_neg(a); a += b, --h);

          //
          T l((T(a.v_[k] << hwbits) | T(a.v_[k - 1] >> hwbits)) / B);
          if (l >> hwbits) [[unlikely]] l = dmax;

          for (a -= hwmul(lshr<hwbits>(b), l); is_neg(a); a += b, --l);

          //
          q.v_[k - N] = l | h << hwbits;
        }
        while (N != k);
      }
    }

    //
    if constexpr(Rem)
    {
      lshr(a, CB);

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
          return wshl<N>(intt<T, M, F...>(a)).naidiv(b);
        }
      );

      std::size_t C;

      intt<T, M, F...> b;

      {
        auto const tmp(negb ? -o : o);

        C = clz(tmp);
        b = {tmp, direct{}};
      }

      lshl(b, C);

      //auto xn(coeff<wshl<N>(intt<T, M, F...>(direct{}, T(2)))>() - b);

      auto xn(
        coeff<make_coeff(48, 17)>() -
        newmul<N>(b, coeff<make_coeff(32, 17)>())
      );

      {
        auto const k(coeff<wshl<N>(intt<T, M, F...>(direct{}, T(2)))>());

        // x_n = x_n(2 - a*x_n)
        for (intt<T, M, F...> tmp; tmp = newmul<N>(b, xn), tmp.v_[N - 1];)
        {
          xn = newmul<N>(xn, k - tmp);
        }
      }

      q = lshr(
          newmul<N>(
            intt<T, M, F...>{nega ? -*this : *this, direct{}},
            xn
          ),
          N * wbits - C
        );
    }

    //
    if constexpr(Rem)
    {
      auto const r((nega ? -*this : *this) - q * (negb ? -o : o));

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
    auto const nega(is_neg(*this)), negb(is_neg(o));
    intt q{};

    intt<T, 2 * N, F...> r;

    //
    {
      decltype(r) D;

      std::size_t CB;

      {
        auto const tmp(negb ? -o : o);

        CB = clz(tmp);
        wshl<N>(D = {tmp, direct{}});
      }

      std::size_t CA;

      {
        auto const tmp(nega ? -*this : *this);

        CA = clz(tmp);
        r = {tmp, direct{}};
      }

      // Na = Nq + Nb; Nq = Na - Nb = N * wbits - CA - (N * wbits - CB) = CB - CA
      if (CB >= CA) [[likely]]
      {
        auto i(CB - CA + 1);

        lshl(r, bits - i);

        do
        {
          if (--i; ucompare(lshl<1>(r), D) >= 0)
          {
            set_bit(q, i);
            r -= D;
          }
        }
        while (i);
      }
      else if constexpr(Rem)
      {
        return *this;
      }
    }

    //
    if constexpr(Rem)
    {
      intt const tmp(wshr<N>(r), direct{});

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
        return ((v_[I] == o.v_[I]) && ...);
      }(std::make_index_sequence<N>());
  }

  constexpr auto operator<=>(intt const& o) const noexcept
  {
    auto const c(is_neg(o) <=> is_neg(*this));

    return c == 0 ? ucompare(*this, o) : c;
  }

  //
  static constexpr auto max() noexcept { return coeff<lshr<1>(~intt{})>(); }
  static constexpr auto min() noexcept { return coeff<~max()>(); }
};

// type promotions
#define INTT_TYPE_PROMOTION__(OP)\
template <typename A, std::size_t M, typename B,\
  std::size_t N, enum feat ...F, enum feat ...G>\
constexpr auto operator OP (intt<A, M, F...> const& a,\
  intt<B, N, G...> const& b) noexcept\
{\
  if constexpr(M * detail::bit_size_v<A> < N * detail::bit_size_v<B>)\
    return intt<B, N, G...>(a) OP b;\
  else\
    return a OP intt<A, M, F...>(b);\
}

INTT_TYPE_PROMOTION__(+)
INTT_TYPE_PROMOTION__(-)
INTT_TYPE_PROMOTION__(*)
INTT_TYPE_PROMOTION__(/)
INTT_TYPE_PROMOTION__(<=>)
INTT_TYPE_PROMOTION__(==)

// conversions
#define INTT_LEFT_CONVERSION__(OP)\
template <typename A, std::size_t B, enum feat... F, typename U>\
constexpr auto operator OP (U&& a, intt<A, B, F...> const& b) noexcept\
  requires(std::is_enum_v<std::remove_cvref_t<U>> ||\
    std::is_integral_v<std::remove_cvref_t<U>>)\
{\
  return intt<A, B, F...>(std::forward<U>(a)) OP b;\
}

INTT_LEFT_CONVERSION__(&)
INTT_LEFT_CONVERSION__(|)
INTT_LEFT_CONVERSION__(^)
INTT_LEFT_CONVERSION__(+)
INTT_LEFT_CONVERSION__(-)
INTT_LEFT_CONVERSION__(*)
INTT_LEFT_CONVERSION__(/)
INTT_LEFT_CONVERSION__(%)
INTT_LEFT_CONVERSION__(==)
INTT_LEFT_CONVERSION__(!=)
INTT_LEFT_CONVERSION__(<)
INTT_LEFT_CONVERSION__(<=)
INTT_LEFT_CONVERSION__(>)
INTT_LEFT_CONVERSION__(>=)
INTT_LEFT_CONVERSION__(<=>)

#define INTT_RIGHT_CONVERSION__(OP)\
template <typename A, std::size_t B, enum feat...F, typename U>\
constexpr auto operator OP (intt<A, B, F...> const& a, U&& b) noexcept\
  requires(std::is_enum_v<std::remove_cvref_t<U>> ||\
    std::is_integral_v<std::remove_cvref_t<U>>)\
{\
  return a OP intt<A, B, F...>(std::forward<U>(b));\
}

INTT_RIGHT_CONVERSION__(&)
INTT_RIGHT_CONVERSION__(|)
INTT_RIGHT_CONVERSION__(^)
INTT_RIGHT_CONVERSION__(+)
INTT_RIGHT_CONVERSION__(-)
INTT_RIGHT_CONVERSION__(*)
INTT_RIGHT_CONVERSION__(/)
INTT_RIGHT_CONVERSION__(%)
INTT_RIGHT_CONVERSION__(==)
INTT_RIGHT_CONVERSION__(!=)
INTT_RIGHT_CONVERSION__(<)
INTT_RIGHT_CONVERSION__(<=)
INTT_RIGHT_CONVERSION__(>)
INTT_RIGHT_CONVERSION__(>=)
INTT_RIGHT_CONVERSION__(<=>)

//utilities///////////////////////////////////////////////////////////////////
constexpr bool is_neg(intt_concept auto const& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using S = std::make_signed_t<typename U::value_type>;

  return S(a.v_[U::words - 1]) < S{};
}

constexpr bool is_neg(std::integral auto const a) noexcept
{
  return a < decltype(a){};
}

constexpr auto abs(intt_concept auto const& a) noexcept
{
  return is_neg(a) ? -a : a;
}

#if defined(__STRICT_ANSI__) && defined (__SIZEOF_INT128__)
constexpr bool is_neg(unsigned __int128) noexcept { return {}; }
constexpr bool is_neg(__int128 const a) noexcept { return a < decltype(a){}; }

constexpr std::size_t clz(unsigned __int128 const a) noexcept
{
  std::uint64_t const lo(a), hi(a >> 64);
  int const r[]{__builtin_clzll(hi), __builtin_clzll(lo) + 64, 128};
  return r[!hi + (!lo && !hi)];
}
#endif

constexpr std::size_t clz(std::integral auto const a) noexcept
{
  return std::countl_zero(std::make_unsigned_t<decltype(a)>(a));
}

constexpr std::size_t clz(intt_concept auto const& a) noexcept
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
    } while ((U::wbits == c) && I);
  }

  return r;
}

constexpr void set_bit(intt_concept auto& a, std::size_t const i) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;
  a.v_[i / U::wbits] |= T{1} << i % U::wbits;
}

template <std::size_t I>
constexpr bool test_bit(intt_concept auto const& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;
  return a.v_[I / U::wbits] & T{1} << I % U::wbits;
}

constexpr auto hwmul(intt_concept auto const& a,
  typename std::remove_cvref_t<decltype(a)>::H const k) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;
  using D = typename U::D;
  using H = typename U::H;

  enum : std::size_t
  {
    M = 2 * U::words,
    N = U::words,
    wbits = U::wbits,
    hwbits = wbits / 2
  };

  U r{};

  if constexpr(std::is_same_v<T, std::uintmax_t>)
  { // multiplying half-words, wbits per iteration
    [&]<auto ...S>(std::index_sequence<S...>) noexcept
    {
      (
        [&]() noexcept
        {
          T const pp(
            T(k) * H(a.v_[S / 2] >> (S % 2 ? std::size_t(hwbits) : 0))
          );

          if constexpr((S % 2) && (M - 1 == S))
          {
            add_words<S / 2>(r, {pp << hwbits});
          }
          else if constexpr(S % 2)
          {
            add_words<S / 2>(r, {pp << hwbits, pp >> hwbits});
          }
          else
          {
            add_words<S / 2>(r, {pp});
          }
        }(),
        ...
      );
    }(std::make_index_sequence<M>());
  }
  else
  { // multiplying words, 2 * wbits per iteration
    [&]<auto ...S>(std::index_sequence<S...>) noexcept
    {
      (
        [&]() noexcept
        {
          D const pp(D(k) * a.v_[S]);

          if constexpr(N - 1 == S)
          {
            add_words<S>(r, {T(pp)});
          }
          else
          {
            add_words<S>(r, {T(pp), T(pp >> wbits)});
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
constexpr auto newmul(intt_concept auto const& a, decltype(a) b) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;
  using D = typename U::D;
  using H = typename U::H;

  enum : std::size_t { N = U::words };

  auto const nega(is_neg(a)), negb(is_neg(b));

  U r{};

  if constexpr(std::is_same_v<T, std::uintmax_t>)
  {
    enum : std::size_t { M = 2 * O, hwbits = U::wbits / 2 };

    for (std::size_t i{}; M != i; ++i)
    {
      for (std::size_t j{}; M != j; ++j)
      {
        T const pp(T(H(a.v_[i / 2] >> (i % 2 ? std::size_t(hwbits) : 0))) *
          H(b.v_[j / 2] >> (j % 2 ? std::size_t(hwbits) : 0)));

        auto const S(i + j);

        S % 2 ?
          add_words(r, S / 2, {pp << hwbits, pp >> hwbits}) :
          add_words(r, S / 2, {pp});
      }
    }
  }
  else
  {
    for (std::size_t i{}; O != i; ++i)
    {
      for (std::size_t j{}; O != j; ++j)
      {
        D const pp(D(a.v_[i]) * b.v_[j]);

        add_words(r, i + j, {T(pp), T(pp >> U::wbits)});
      }
    }
  }

  //
  wshr<O>(r);

  r.v_[O] = a.v_[O] * b.v_[O];

  if (nega != negb)
  {
    for (auto i{O + 1}; N != i; r.v_[i++] = ~T{});
  }

  if (a.v_[O])
  {
    if (intt<T, O> const bb(b, direct{}); nega)
    {
      auto A{-a.v_[O]};
      do sub_words<0>(r, bb.v_); while (--A);
    }
    else
    {
      auto A{a.v_[O]};
      do add_words<0>(r, bb.v_); while (--A);
    }
  }

  if (b.v_[O])
  {
    if (intt<T, O> const aa(a, direct{}); negb)
    {
      auto B{-b.v_[O]};
      do sub_words<0>(r, aa.v_); while (--B);
    }
    else
    {
      auto B{b.v_[O]};
      do add_words<0>(r, aa.v_); while (--B);
    }
  }

  //
  return r;
}

template <std::size_t M>
constexpr auto& lshl(intt_concept auto&& a) noexcept
  requires(bool(M) && (M < std::remove_cvref_t<decltype(a)>::wbits))
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
  }(std::make_index_sequence<N - 1>());

  return *a.v_ <<= M, a;
}

constexpr auto& lshl(intt_concept auto&& a, std::size_t M) noexcept
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
      shl(U::wbits - 1, std::make_index_sequence<N - 1>());
    }

    shl(M, std::make_index_sequence<N - 1>());
  }

  return a;
}

template <std::size_t M>
constexpr auto& lshr(intt_concept auto&& a) noexcept
  requires(bool(M) && (M < std::remove_cvref_t<decltype(a)>::wbits))
{
  using U = std::remove_cvref_t<decltype(a)>;

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (
        a.v_[I] = (a.v_[I + 1] << (U::wbits - M)) | (a.v_[I] >> M)
      ),
      ...
    );
  }(std::make_index_sequence<U::words - 1>());

  return a.v_[U::words - 1] >>= M, a;
}

constexpr auto& lshr(intt_concept auto&& a, std::size_t M) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;

  enum : std::size_t {N = U::words};

  if (M)
  {
    auto const shr([&]<auto ...I>(auto const e,
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
      shr(U::wbits - 1, std::make_index_sequence<N - 1>());
    }

    shr(M, std::make_index_sequence<N - 1>());
  }

  return a;
}

template <std::size_t M> requires(bool(M))
constexpr auto& wshl(intt_concept auto&& a) noexcept
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

constexpr auto& wshl(intt_concept auto&& a, std::size_t const M) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;

  std::size_t i{};

  for (auto const J(U::words - M); i != J; ++i) a.v_[i + M] = a.v_[i];
  for (; i != U::words;) a.v_[U::words - ++i] = {};

  return a;
}

template <std::size_t M> requires(bool(M))
constexpr auto& wshr(intt_concept auto&& a) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;
  using T = typename U::value_type;

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    (
      (a.v_[I] = M + I < U::words ? a.v_[I + M] : T{}),
      ...
    );
  }(std::make_index_sequence<U::words>());

  return a;
}

constexpr auto& wshr(intt_concept auto&& a, std::size_t const M) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;

  std::size_t i{};

  for (auto const J(U::words - M); i != J; ++i) a.v_[i] = a.v_[i + M];
  for (; i != U::words;) a.v_[i++] = {};

  return a;
}

constexpr auto ucompare(intt_concept auto const& a, decltype(a) b) noexcept
{
  using U = std::remove_cvref_t<decltype(a)>;

  detail::underlying_type_t<decltype(U::words)> i{U::words};

  do
  {
    --i;

    if (auto const c(a[i] <=> b[i]); c != 0) return c;
  }
  while (i);

  return std::strong_ordering::equal;
}

template <std::size_t S, std::size_t M>
constexpr void add_words(intt_concept auto& a,
  typename std::remove_cvref_t<decltype(a)>::value_type const (&w)[M])
  noexcept requires(bool(M) && (S < std::remove_cvref_t<decltype(a)>::words))
{
  using U = std::remove_cvref_t<decltype(a)>;

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    bool c;

    (
      [&]() noexcept
      {
        auto& s(a.v_[S + I]);

        if constexpr(!I)
        {
          auto const b(*w);

          c = (s += b) < b;
        }
        else if constexpr(I < M)
        {
          auto const b(w[I]);

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
  }(std::make_index_sequence<U::words - S>());
}

template <std::size_t M>
constexpr void add_words(intt_concept auto& a, std::size_t i,
  typename std::remove_cvref_t<decltype(a)>::value_type const (&w)[M])
  noexcept requires(bool(M))
{
  using U = std::remove_cvref_t<decltype(a)>;

  bool c;

  {
    auto const b(*w);

    c = (a.v_[i++] += b) < b;
  }

  for (std::size_t j(1); (M != j) && (U::words != i);)
  {
    auto& s(a.v_[i++]);
    auto const b(w[j++]);

    s += c + b;
    c = c ? s <= b : s < b;
  }

  while (U::words != i) c = (a.v_[i++] += c) < c;
}

template <std::size_t S, std::size_t M>
constexpr void sub_words(intt_concept auto& a,
  typename std::remove_cvref_t<decltype(a)>::value_type const (&w)[M])
  noexcept requires(bool(M) && (S < std::remove_cvref_t<decltype(a)>::words))
{
  using U = std::remove_cvref_t<decltype(a)>;
  static_assert(S < U::words);

  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    bool c;

    (
      [&]() noexcept
      {
        auto& d(a.v_[S + I]);
        auto const a(d);

        if constexpr(!I)
        {
          c = (d -= *w) > a;
        }
        else if constexpr(I < M)
        {
          d = d - w[I] - c;
          c = c ? d >= a : d > a;
        }
        else
        {
          c = (d -= c) > a;
        }
      }(),
      ...
    );
  }(std::make_index_sequence<U::words - S>());
}

constexpr auto seqsqrt(intt_concept auto const& a) noexcept
{ // CR = CR + (N * wbits - CR) / 2;
  using U = std::remove_cvref_t<decltype(a)>;

  detail::double_t<U> r(a, direct{}), Q{};

  auto const CR((U::bits + clz(a)) / 2);
  lshl(r, CR);

  for (auto i(2 * U::bits - CR); U::bits != i;)
  {
    if (auto tmp(Q); set_bit(lshl<1>(tmp), --i),
      ucompare(lshl<1>(r), tmp) >= 0)
    {
      set_bit(Q, i);
      r -= tmp;
    }
  }

  //
  return U{wshr<U::words>(Q), direct{}};
}

//
template <typename T>
constexpr std::pair<T, bool> to_integral(std::input_iterator auto i,
  decltype(i) const end) noexcept
{
  if (T r{}; i == end) [[unlikely]]
  {
    return {r, true};
  }
  else [[likely]]
  {
    bool neg{};

    switch (*i)
    {
      [[likely]] case '0': case '1': case '2': case '3': case '4':
      case '5': case '6': case '7': case '8': case '9':
        break;

      case '-':
        neg = true;
        [[fallthrough]];

      case '+':
        ++i;
        break;

      [[unlikely]] default:
        return {r, true};
    }

    //
    for (; end != i; ++i)
    {
      switch (*i)
      {
        [[likely]] case '0': case '1': case '2': case '3': case '4':
        case '5': case '6': case '7': case '8': case '9':
          if (r >= coeff<T::min() / 10>()) [[likely]]
          {
            if (decltype(r) const t(10 * r), d(*i - '0');
              t >= T::min() + d) [[likely]]
            {
              r = t - d;

              continue;
            }
          }

          return {r, true};

        case '\0':
          break;

        [[unlikely]] default:
          return {r, true};
      }

      break;
    }

    //
    return {neg ? r : -r, !neg && (T::min() == r)}; // can return error
  }
}

template <typename T>
constexpr auto to_integral(auto const& s) noexcept ->
  decltype(std::cbegin(s), std::cend(s), std::pair<T, bool>())
{
  return to_integral<T>(std::cbegin(s), std::cend(s));
}

template <typename T, std::size_t N, enum feat... FF>
constexpr auto to_pair(intt<T, N, FF...> a,
  decltype(a) const k = 10u) noexcept
{
  char data[detail::num_digits(decltype(a)::bits - 1) + 1];
  auto i(std::size(data) - 1);

  //
  decltype(auto) A{"0123456789abcdef"};

  do
  {
    data[i--] = A[std::abs((signed char)(a % k))];
    a /= k;
  }
  while (a);

  data[i] = '-';

  //
  return std::pair(i, std::to_array(std::move(data)));
}

constexpr auto to_string(intt_concept auto const& a)
{
  auto const& [i, arr](to_pair(a));

  return std::string(arr.begin() + (i + !is_neg(a)), arr.end());
}

inline auto& operator<<(std::ostream& os, intt_concept auto const& a)
{
  auto const f(os.flags());

  auto const& [i, arr](
    to_pair(
      a,
      f & std::ios_base::dec ? 10u :
      f & std::ios_base::hex ? 16u :
      f & std::ios_base::oct ? 8u : 10u
    )
  );

  return os << std::string_view(arr.begin() + (i + !is_neg(a)), arr.end());
}

}

namespace std
{

template <typename U> requires(intt::intt_concept<U>)
struct hash<U>
{
  using T = typename U::value_type;

  constexpr auto operator()(auto const& a) const
    noexcept(noexcept(std::hash<T>()(std::declval<T const&>())))
  {
    return [&]<auto ...I>(auto&& s, std::index_sequence<I...>)
      noexcept(noexcept(std::hash<T>()(std::declval<T const&>())))
      {
        return ((s ^= std::hash<T>()(a[I + 1]) + intt::magic::ISR +
          (s << 6) + (s >> 2)), ...), s;
      }(std::hash<T>()(a[0]), std::make_index_sequence<U::words - 1>());
  }
};

}

#endif // INTT_HPP
