#ifndef INTT_DEBUG_HPP
# define INTT_DEBUG_HPP
# pragma once

#include <cassert>
#include <cmath>
#include <iomanip> // std::hex
#include <sstream>

#include "arith.hpp"

namespace ar
{

template <std::size_t M>
constexpr auto to_double(uarray_c auto const& a) noexcept
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { N = size<decltype(a)>(), wbits = bit_size_v<T> };

  using F = double;

  return is_neg(a) ?
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return -(((T(~a.v_[I]) *
        std::ldexp(F(1), (int(I) - int(M)) * int(wbits))) + ...) +
        std::ldexp(F(1), -int(M) * int(wbits)));
    }(std::make_index_sequence<N>()) :
    [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return ((a.v_[I] *
        std::ldexp(F(1), (int(I) - int(M)) * int(wbits))) + ...);
    }(std::make_index_sequence<N>());
}

auto to_raw(uarray_c auto const& a)
{
  using T = std::remove_cvref_t<decltype(a[0])>;
  enum : std::size_t { N = size<decltype(a)>(), wbits = bit_size_v<T> };

  using V = std::conditional_t<std::is_same_v<T, std::uint8_t>, unsigned, T>;

  std::stringstream ss;

  ss << '"' << std::hex << std::setfill('0');

  for (auto i(N - 1); i; --i)
    ss << std::setw(sizeof(T) * 2) << V(a[i]) << " ";

  ss << std::setw(sizeof(T) * 2) << V(a[0]) << '"';

  return ss.str();
}

}

#endif // INTT_DEBUG_HPP
