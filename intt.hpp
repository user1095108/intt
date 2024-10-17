#ifndef INTT_HPP
# define INTT_HPP
# pragma once

#include <cmath> // std::ldexp()
#include <algorithm> // std::max()
#include <functional> // std::hash
#include <iterator> // std::begin(), std::end()
#include <ostream>

#include "constants.hpp"
#include "naidiv.hpp"
#include "newdiv.hpp"
#include "naimul.hpp"
#include "naisqrt.hpp"

namespace intt
{

struct direct_t { explicit direct_t() = default; };
inline constexpr direct_t direct{};

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

namespace detail
{

template <typename> struct is_intt : std::false_type {};

template <std::unsigned_integral T, std::size_t N, enum feat ...F>
struct is_intt<intt<T, N, F...>> : std::true_type {};

}

template <typename T>
constexpr auto is_intt_v{detail::is_intt<std::remove_cv_t<T>>::value};

template <typename T> concept is_intt_c = is_intt_v<T>;

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

  ar::array_t<T, N> v_;

  intt() = default;

  intt(intt const&) = default;
  intt(intt&&) = default;

  constexpr intt(direct_t, auto&& ...a) noexcept:
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
            v_[I] = I * wbits < ar::bit_size_v<U> ? v >> I * wbits : T{}
          ),
          ...
        );
      }
    }(std::make_index_sequence<N>());
  }

  template <std::size_t M, enum feat ...FF>
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

  template <std::size_t M, enum feat ...FF>
  constexpr intt(intt<T, M, FF...> const& o, direct_t) noexcept
  {
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      (
        (v_[I] = I < M ? o.v_[I] : T{}),
        ...
      );
    }(std::make_index_sequence<N>());
  }

  template <typename U, std::size_t M, enum feat ...FF>
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

  constexpr auto& operator &=(intt const& a) noexcept
  {
    ar::and_(v_, a.v_); return *this;
  }

  constexpr auto& operator |=(intt const& a) noexcept
  {
    ar::or_(v_, a.v_); return *this;
  }

  constexpr auto& operator ^=(intt const& a) noexcept
  {
    ar::xor_(v_, a.v_); return *this;
  }

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

  constexpr auto& operator*=(intt const& o) noexcept
  {
    if constexpr(detail::contains<F...>(SEQMUL))
    {
      ar::seqmul(v_, o.v_);
    }
    else
    {
      ar::naimul(v_, o.v_);
    }

    return *this;
  }

  constexpr auto& operator/=(intt const& o) noexcept
  {
    auto const s(ar::is_neg(v_) != ar::is_neg(o.v_));

    if (ar::is_neg(v_)) ar::neg(v_);

    if constexpr(decltype(v_) B; detail::contains<F...>(GLDDIV))
    {
      ar::glddiv<false>(
        v_,
        ar::is_neg(o.v_) ? ar::copy(B, o.v_), ar::neg(B), B : o.v_
      );
    }
    else if constexpr(detail::contains<F...>(NEWDIV))
    {
      ar::newdiv<false>(
        v_,
        ar::is_neg(o.v_) ? ar::copy(B, o.v_), ar::neg(B), B : o.v_
      );
    }
    else if constexpr(detail::contains<F...>(SEQDIV))
    {
      ar::seqdiv<false>(
        v_,
        ar::is_neg(o.v_) ? ar::copy(B, o.v_), ar::neg(B), B : o.v_
      );
    }
    else
    {
      ar::naidiv<false>(
        v_,
        ar::is_neg(o.v_) ? ar::copy(B, o.v_), ar::neg(B), B : o.v_
      );
    }

    if (s) ar::neg(v_);

    return *this;
  }

  constexpr auto& operator%=(intt const& o) noexcept
  {
    auto const s(ar::is_neg(v_));

    if (ar::is_neg(v_)) ar::neg(v_);

    if constexpr(decltype(v_) B; detail::contains<F...>(GLDDIV))
    {
      ar::glddiv<true>(
        v_,
        ar::is_neg(o.v_) ? ar::copy(B, o.v_), ar::neg(B), B : o.v_
      );
    }
    else if constexpr(detail::contains<F...>(NEWDIV))
    {
      ar::newdiv<true>(
        v_,
        ar::is_neg(o.v_) ? ar::copy(B, o.v_), ar::neg(B), B : o.v_
      );
    }
    else if constexpr(detail::contains<F...>(SEQDIV))
    {
      ar::seqdiv<true>(
        v_,
        ar::is_neg(o.v_) ? ar::copy(B, o.v_), ar::neg(B), B : o.v_
      );
    }
    else
    {
      ar::naidiv<true>(
        v_,
        ar::is_neg(o.v_) ? ar::copy(B, o.v_), ar::neg(B), B : o.v_
      );
    }

    if (s) ar::neg(v_);

    return *this;
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
          return v_[0];
        }
      }(std::make_index_sequence<ar::bit_size_v<U> / wbits>());
  }

  //
  constexpr T operator[](std::size_t const i) const noexcept { return v_[i]; }

  //
  static constexpr auto size() noexcept { return N; }

  // bitwise
  constexpr auto operator~() const noexcept
  {
    auto r(*this); ar::not_(r.v_); return r;
  }

  constexpr auto operator&(intt const& o) const noexcept
  {
    auto r(*this); ar::and_(r.v_, o.v_); return r;
  }

  constexpr auto operator|(intt const& o) const noexcept
  {
    auto r(*this); ar::or_(r.v_, o.v_); return r;
  }

  constexpr auto operator^(intt const& o) const noexcept
  {
    auto r(*this); ar::xor_(r.v_, o.v_); return r;
  }

  constexpr auto operator<<(std::integral auto M) const noexcept
  {
    auto r(*this); ar::lshl(r.v_, M); return r;
  }

  constexpr auto operator>>(std::integral auto M) const noexcept
  {
    auto r(*this); ar::ashr(r.v_, M); return r;
  }

  // increment, decrement
  constexpr auto& operator++() noexcept
  {
    ar::add(v_, ar::array_t<T, 1>{T(1)}); return *this;
  }

  constexpr auto& operator--() noexcept
  {
    ar::sub(v_, ar::array_t<T, 1>{T(1)}); return *this;
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
    auto r(*this); r *= o; return r;
  }

  constexpr auto operator/(intt const& o) const noexcept
  {
    auto r(*this); r /= o; return r;
  }

  constexpr auto operator%(intt const& o) const noexcept
  {
    auto r(*this); r %= o; return r;
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
  static constexpr auto max() noexcept {return ar::coeff<lshr<1>(~intt{})>();}
  static constexpr auto min() noexcept {return ar::coeff<~max()>();}
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
constexpr bool is_neg(is_intt_c auto const& a) noexcept
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

constexpr auto abs(is_intt_c auto const& a) noexcept
{
  return is_neg(a) ? -a : a;
}

template <std::size_t M> requires(bool(M))
constexpr auto&& lshr(is_intt_c auto&& a) noexcept
{
  ar::lshr<M>(a.v_); return a;
}

constexpr auto&& lshr(is_intt_c auto&& a, std::size_t const M) noexcept
{
  ar::lshr(a.v_, M); return a;
}

//
constexpr auto isqrt(is_intt_c auto const& a) noexcept
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
          if (r >= ar::coeff<T::min() / 10>()) [[likely]]
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

constexpr auto& to_array(is_intt_c auto const& a) noexcept { return a.v_; }

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

constexpr auto to_string(is_intt_c auto const& a)
{
  auto const& [i, arr](to_pair(a));

  return std::string(arr.begin() + (i + !is_neg(a)), arr.end());
}

inline auto& operator<<(std::ostream& os, is_intt_c auto const& a)
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

template <typename U> requires (intt::is_intt_v<U>)
struct hash<U>
{
  using T = typename U::value_type;

  constexpr auto operator()(auto const& a) const
    noexcept(noexcept(std::hash<T>()(std::declval<T const&>())))
  {
    return [&]<auto ...I>(auto&& s, std::index_sequence<I...>)
      noexcept(noexcept(std::hash<T>()(std::declval<T const&>())))
      {
        return ((s ^= std::hash<T>()(a[I + 1]) + intt::consts::ISR +
          (s << 6) + (s >> 2)), ...), s;
      }(std::hash<T>()(a[0]), std::make_index_sequence<U::words - 1>());
  }
};

}

#endif // INTT_HPP
