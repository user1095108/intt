#ifndef INTT_MAGIC_HPP
# define INTT_MAGIC_HPP
# pragma once

#include <climits> // CHAR_BIT
#include <cstddef> // std::size_t
#include <cstdint> // std::uint8_t
#include <utility> // std::index_sequence

namespace intt::magic
{

namespace detail
{

// inverse golden ratio
static constexpr std::uint8_t const igr_c[]{
  0x9E, 0x37, 0x79, 0xB9, 0x7F, 0x4A, 0x7C, 0x15,
  0xF3, 0x9C, 0xC0, 0x60, 0x5C, 0xED, 0xC8, 0x34,
  0x10, 0x82, 0x27, 0x6B, 0xF3, 0xA2, 0x72, 0x51,
  0xF8, 0x6C, 0x6A, 0x11, 0xD0, 0xC1, 0x8E, 0x95,
  0x27, 0x67, 0xF0, 0xB1, 0x53, 0xD2, 0x7B, 0x7F,
  0x03, 0x47, 0x04, 0x5B, 0x5B, 0xF1, 0x82, 0x7F,
  0x01, 0x88, 0x6F, 0x09, 0x28, 0x40, 0x30, 0x02,
  0xC1, 0xD6, 0x4B, 0xA4, 0x0F, 0x33, 0x5E, 0x36
};

// inverse silver ratio
static constexpr std::uint8_t const isr_c[]{
  0x6A, 0x09, 0xE6, 0x67, 0xF3, 0xBC, 0xC9, 0x08,
  0xB2, 0xFB, 0x13, 0x66, 0xEA, 0x95, 0x7D, 0x3E,
  0x3A, 0xDE, 0xC1, 0x75, 0x12, 0x77, 0x50, 0x99,
  0xDA, 0x2F, 0x59, 0x0B, 0x06, 0x67, 0x32, 0x2A, 
  0x95, 0xF9, 0x06, 0x08, 0x75, 0x71, 0x45, 0x87,
  0x51, 0x63, 0xFC, 0xDF, 0xB9, 0x07, 0xB6, 0x72,
  0x1E, 0xE9, 0x50, 0xBC, 0x87, 0x38, 0xF6, 0x94,
  0xF0, 0x09, 0x0E, 0x6C, 0x7B, 0xF4, 0x4E, 0xD1
};

template <typename T, auto A>
consteval T generate_constant() noexcept
{
  return []<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return ((T(A[I]) << (sizeof(T) - 1 - I) * CHAR_BIT) | ...);
    }(std::make_index_sequence<sizeof(T)>());
}

}

enum : std::size_t
{
  IGR = detail::generate_constant<std::size_t, detail::igr_c>(),
  ISR = detail::generate_constant<std::size_t, detail::isr_c>(),
};

}

#endif // INTT_MAGIC_HPP
