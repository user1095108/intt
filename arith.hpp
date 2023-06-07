#include <climits> // CHAR_BIT
#include <cstddef> // std::size_t
#include <bit> // std::countl_zero
#include <concepts> // std::floating_point, std::integral
#include <type_traits> // std::make_unsigned()
#include <utility> // std::index_sequence

namespace ar
{ // provides ops on arrays of unsigned ints

template <typename U>
static constexpr std::size_t bit_size_v(CHAR_BIT * sizeof(U));

//
template <std::unsigned_integral T, std::size_t N>
constexpr bool any(T const(&a)[N]) noexcept
{
  return [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return (a[I] || ...);
    }(std::make_index_sequence<N>());
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto eq(T const(&a)[N], T const(&b)[N]) noexcept
{
  return [&]<auto ...I>(std::index_sequence<I...>) noexcept
    {
      return ((a[I] == b[I]) && ...);
    }(std::make_index_sequence<N>());
}

template <std::unsigned_integral T, std::size_t N>
constexpr auto ucmp(T const(&a)[N], T const(&b)[N]) noexcept
{
  auto i(N);

  do
  {
    --i;

    if (auto const c(a[i] <=> b[i]); c != 0) return c;
  }
  while (i);

  return std::strong_ordering::equal;
}

template <std::unsigned_integral T, std::size_t N>
constexpr bool is_neg(T const(&a)[N]) noexcept
{
  using S = std::make_signed_t<T>;
  return S(a[N - 1]) < S{};
}

constexpr bool is_neg(std::integral auto const a) noexcept
{
  return a < decltype(a){};
}

//
constexpr std::size_t clz(std::signed_integral auto const a) noexcept
{
  return std::countl_zero(std::make_unsigned_t<decltype(a)>(a));
}

constexpr std::size_t clz(std::unsigned_integral auto const a) noexcept
{
  return std::countl_zero(a);
}

template <std::unsigned_integral T, std::size_t N>
constexpr std::size_t clz(T const(&a)[N]) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  decltype(N) r{};

  {
    auto i(N);

    int c;

    do
    {
      r += c = std::countl_zero(a[--i]);
    } while ((wbits == c) && i);
  }

  return r;
}

//
template <std::unsigned_integral T, std::size_t N>
constexpr void lshl(T (&a)[N], std::size_t M) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  if (M)
  {
    auto const shl([&]<auto ...I>(auto const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            a[N - 1 - I] = (a[N - 1 - I] << e) |
              (a[N - 1 - I - 1] >> (wbits - e))
          ),
          ...
        );

        *a <<= e;
      }
    );

    for (; M >= wbits; M -= wbits - 1)
    {
      shl(wbits - 1, std::make_index_sequence<N - 1>());
    }

    shl(M, std::make_index_sequence<N - 1>());
  }
}

template <std::unsigned_integral T, std::size_t N>
constexpr void ashr(T (&a)[N], std::size_t M) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };

  if (M)
  {
    auto const shr([neg(is_neg(a)), &a]<auto ...I>(auto const e,
      std::index_sequence<I...>) noexcept
      {
        (
          (
            a[I] = (a[I] >> e) | (a[I + 1] << (wbits - e))
          ),
          ...
        );

        a[N - 1] = (a[N - 1] >> e) | (neg ? ~T{} << (wbits - e) : T{});
      }
    );

    for (; M >= wbits; M -= wbits - 1)
    {
      shr(wbits - 1, std::make_index_sequence<N - 1>());
    }

    shr(M, std::make_index_sequence<N - 1>());
  }
}

template <std::unsigned_integral T, std::size_t N>
constexpr void set_bit(T (&a)[N], std::size_t const i) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };
  a[i / wbits] |= T{1} << i % wbits;
}

template <std::size_t I, std::unsigned_integral T, std::size_t N>
constexpr bool test_bit(T const (&a)[N]) noexcept
{
  enum : std::size_t { wbits = bit_size_v<T> };
  return a[I / wbits] & T{1} << I % wbits;
}

//
template <std::unsigned_integral T, std::size_t N>
constexpr void neg(T (&a)[N]) noexcept
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    bool c{true};

    ((c = (a[I] = T(~a[I]) + c) < c), ...);
  }(std::make_index_sequence<N>());
}

template <std::unsigned_integral T, std::size_t N>
constexpr void not_(T (&a)[N]) noexcept
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    ((a[I] = T(~a[I])), ...);
  }(std::make_index_sequence<N>());
}

template <std::size_t S = 0, std::unsigned_integral T,
  std::size_t N0, std::size_t N1>
constexpr void add(T (&a)[N0], T const (&b)[N1]) noexcept
  requires(S < N0)
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    bool c;

    (
      [&]() noexcept
      {
        auto& s(a[S + I]);
        auto const a(s);

        if constexpr(!I)
        {
          c = (s += *b) < a;
        }
        else if constexpr(I < N1)
        {
          s += c + b[I];
          c = c ? s <= a : s < a;
        }
        else
        {
          c = (s += c) < c;
        }
      }(),
      ...
    );
  }(std::make_index_sequence<N0 - S>());
}

template <std::unsigned_integral T, std::size_t N0, std::size_t N1>
constexpr void add(T (&a)[N0], T const (&b)[N1], std::size_t i) noexcept
{
  bool c;

  {
    auto const b0(*b);

    c = (a[i++] += b0) < b0;
  }

  for (std::size_t j(1); (N1 != j) && (N0 != i);)
  {
    auto& s(a[i++]);
    auto const a(s);

    s += c + b[j++];
    c = c ? s <= a : s < a;
  }

  while (N0 != i) c = (a[i++] += c) < c;
}

template <std::size_t S = 0, std::unsigned_integral T,
  std::size_t N0, std::size_t N1>
constexpr void sub(T(&a)[N0], T const (&b)[N1]) noexcept
  requires(S < N0)
{
  [&]<auto ...I>(std::index_sequence<I...>) noexcept
  {
    bool c;

    (
      [&]() noexcept
      {
        auto& d(a[S + I]);
        auto const a(d);

        if constexpr(!I)
        {
          c = (d -= *b) > a;
        }
        else if constexpr(I < N1)
        {
          d = d - b[I] - c;
          c = c ? d >= a : d > a;
        }
        else
        {
          c = (d -= c) > a;
        }
      }(),
      ...
    );
  }(std::make_index_sequence<N0 - S>());
}

}
