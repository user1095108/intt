#ifndef INTT_HPP
# define INTT_HPP
# pragma once

#include <cmath> // std::ldexp()
#include <algorithm> // std::max()
#include <array> // std::to_array()
#include <functional> // std::hash
#include <iterator> // std::begin(), std::end()
#include <ostream>

#include "naisqrt.hpp"
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
        auto const neg(v < U{});

        (
          (
            v_[I] = I * wbits < ar::bit_size_v<U> ?
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
            v_[I] = I * wbits < ar::bit_size_v<U> ?
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
    ar::lshl(v_, i); return *this;
  }

  constexpr auto& operator>>=(std::integral auto const i) noexcept
  {
    ar::ashr(v_, i); return *this;
  }

  constexpr auto& operator+=(intt const& o) noexcept
  {
    ar::add(v_, o.v_); return *this;
  }

  constexpr auto& operator-=(intt const& o) noexcept
  {
    ar::sub(v_, o.v_); return *this;
  }

  //
  constexpr explicit operator bool() const noexcept { return ar::any(v_); }

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
          if constexpr(ar::bit_size_v<U> > N * wbits)
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
      }(std::make_index_sequence<ar::bit_size_v<U> / wbits>());
  }

  //
  constexpr T operator[](std::size_t const i) const noexcept { return v_[i]; }

  //
  static constexpr auto size() noexcept { return N; }
  constexpr auto data() const noexcept { return v_; }

  // bitwise
  constexpr auto operator~() const noexcept
  {
    auto r(*this); ar::not_(r.v_); return r;
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
    auto r(*this); ar::lshl(r.v_, M); return r;
  }

  constexpr auto operator>>(std::integral auto M) const noexcept
  {
    auto r(*this); ar::ashr(r.v_, M); return r;
  }

  // increment, decrement
  constexpr auto& operator++() noexcept { ar::add(v_, {T(1)}); return *this; }
  constexpr auto& operator--() noexcept { ar::sub(v_, {T(1)}); return *this; }

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
    auto r(*this); ar::neg(r.v_); return r;
  }

  //
  constexpr auto operator+(intt const& o) const noexcept
  {
    auto r(*this); ar::add(r.v_, o.v_); return r;
  }

  constexpr auto operator-(intt const& o) const noexcept
  {
    auto r(*this); ar::sub(r.v_, o.v_); return r;
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
            ar::add(r.v_, {pp << hwbits, pp >> hwbits}, S / 2) :
            ar::add(r.v_, {pp}, S / 2);
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

          ar::add(r.v_, {T(pp), T(pp >> wbits)}, S);
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
          if (ar::test_bit<I>(o.v_)) r += A;

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

        C = ar::clz(tmp.v_);
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
      if (ar::ucmp(r.v_, b.v_) >= 0) r -= b;

      return nega ? -r : r;
    }
    else
    {
      if (ar::ucmp(r.v_, b.v_) >= 0) ++q;

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

        CA = ar::clz(tmp.v_);
        a = {tmp, direct{}};
      }

      intt<T, M, F...> b;

      {
        auto const tmp(negb ? -o : o);

        CB = ar::clz(tmp.v_);
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

        C = ar::clz(tmp.v_);
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

        CB = ar::clz(tmp.v_);
        wshl<N>(D = {tmp, direct{}});
      }

      std::size_t CA;

      {
        auto const tmp(nega ? -*this : *this);

        CA = ar::clz(tmp.v_);
        r = {tmp, direct{}};
      }

      // Na = Nq + Nb; Nq = Na - Nb = N * wbits - CA - (N * wbits - CB) = CB - CA
      if (CB >= CA) [[likely]]
      {
        auto i(CB - CA + 1);

        lshl(r, bits - i);

        do
        {
          if (--i; ar::ucmp(lshl<1>(r).v_, D) >= 0)
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
    return ar::eq(v_, o.v_);
  }

  constexpr auto operator<=>(intt const& o) const noexcept
  {
    auto const c(is_neg(o) <=> is_neg(*this));

    return c == 0 ? ar::ucmp(v_, o.v_) : c;
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
  if constexpr(M * ar::bit_size_v<A> < N * ar::bit_size_v<B>)\
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
  return ar::is_neg(a.v_);
}

constexpr bool is_neg(std::integral auto const a) noexcept
{
  return a < decltype(a){};
}

#if defined(__STRICT_ANSI__) && defined (__SIZEOF_INT128__)
constexpr bool is_neg(__int128 const a) noexcept { return a < decltype(a){}; }
constexpr bool is_neg(unsigned __int128) noexcept { return {}; }
#endif

constexpr auto abs(intt_concept auto const& a) noexcept
{
  return is_neg(a) ? -a : a;
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
            ar::add<S / 2>(r.v_, {pp << hwbits});
          }
          else if constexpr(S % 2)
          {
            ar::add<S / 2>(r.v_, {pp << hwbits, pp >> hwbits});
          }
          else
          {
            ar::add<S / 2>(r.v_, {pp});
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
            ar::add<S>(r.v_, {T(pp)});
          }
          else
          {
            ar::add<S>(r.v_, {T(pp), T(pp >> wbits)});
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
          ar::add(r, {pp << hwbits, pp >> hwbits}, S / 2) :
          ar::add(r, {pp}, S / 2);
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

        ar::add(r, {T(pp), T(pp >> U::wbits)}, i + j);
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
      do ar::sub(r.v_, bb.v_); while (--A);
    }
    else
    {
      auto A{a.v_[O]};
      do ar::add(r.v_, bb.v_); while (--A);
    }
  }

  if (b.v_[O])
  {
    if (intt<T, O> const aa(a, direct{}); negb)
    {
      auto B{-b.v_[O]};
      do ar::sub(r.v_, aa.v_); while (--B);
    }
    else
    {
      auto B{b.v_[O]};
      do ar::add(r.v_, aa.v_); while (--B);
    }
  }

  //
  return r;
}

template <std::size_t M> requires(bool(M))
constexpr auto&& lshl(intt_concept auto&& a) noexcept
{
  ar::lshl<M>(a.v_); return a;
}

constexpr auto&& lshl(intt_concept auto&& a, std::size_t const M) noexcept
{
  ar::lshl(a.v_, M); return a;
}

template <std::size_t M> requires(bool(M))
constexpr auto&& lshr(intt_concept auto&& a) noexcept
{
  ar::lshr<M>(a.v_); return a;
}

constexpr auto&& lshr(intt_concept auto&& a, std::size_t const M) noexcept
{
  ar::lshr(a.v_, M); return a;
}

template <std::size_t M> requires(bool(M))
constexpr auto&& wshl(intt_concept auto&& a) noexcept
{
  ar::wshl<M>(a.v_); return a;
}

constexpr auto&& wshl(intt_concept auto&& a, std::size_t const M) noexcept
{
  ar::wshl(a.v_, M); return a;
}

template <std::size_t M> requires(bool(M))
constexpr auto&& wshr(intt_concept auto&& a) noexcept
{
  ar::wshr<M>(a.v_); return a;
}

constexpr auto&& wshr(intt_concept auto&& a, std::size_t const M) noexcept
{
  ar::wshr(a.v_, M); return a;
}

//
constexpr auto isqrt(intt_concept auto const& a) noexcept
{
  auto r(a); ar::seqsqrt(r.v_); return r;
}

//
template <typename T>
constexpr std::pair<T, bool> to_integral(std::input_iterator auto i,
  decltype(i) const end) noexcept
{
  if (T r{}; end == i) [[unlikely]]
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
    data[i--] = A[std::abs(int(a % k))];
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

template <intt::intt_concept U>
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
