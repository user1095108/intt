#ifndef INTT_DEBUG_HPP
# define INTT_DEBUG_HPP
# pragma once

#include <cassert>
#include <iomanip> // std::hex
#include <sstream>

namespace intt
{

template <std::size_t M, typename T, std::size_t N, enum feat... FF>
constexpr auto to_double(intt<T, N, FF...> const& a) noexcept
{
  using F = double;
  using U = std::remove_cvref_t<decltype(a)>;

  return is_neg(a) ?
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return -(((T(~a.v_[I]) *
        std::ldexp(F(1), (int(I) - int(M)) * int(U::wbits))) + ...) +
        std::ldexp(F(1), -int(M) * int(U::wbits)));
    }(std::make_index_sequence<N>()) :
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return ((a.v_[I] *
        std::ldexp(F(1), (int(I) - int(M)) * int(U::wbits))) + ...);
    }(std::make_index_sequence<N>());
}

auto to_raw(intt_concept auto const& a)
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

}

#endif // INTT_DEBUG_HPP
