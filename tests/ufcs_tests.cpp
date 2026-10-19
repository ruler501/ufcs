#include <type_traits>

#include <catch2/catch_test_macros.hpp>

#include "ufcs.hpp"

struct Counter {
  int value = 0;

  constexpr int get() const noexcept { return value; }

  constexpr int add(int amount) const noexcept { return value + amount; }

  constexpr void increment(int amount) noexcept { value += amount; }
};

constexpr int multiply(const Counter &counter, int factor) noexcept { return counter.value * factor; }

struct Property {
  int value = 42;
};

constexpr auto get_u = UFCS(get);
constexpr auto add_u = UFCS(add);
constexpr auto increment_u = UFCS(increment);
constexpr auto multiply_u = UFCS(multiply);

TEST_CASE("dispatches member functions") {
  Counter counter{5};

  STATIC_REQUIRE(noexcept(counter | get_u));
  REQUIRE((counter | get_u) == 5);
}

TEST_CASE("dispatches member functions with arguments") {
  Counter counter{5};

  // STATIC_REQUIRE(noexcept(counter | add_u(3)));
  REQUIRE((counter | add_u(3)) == 8);
}

TEST_CASE("dispatches free functions with arguments") {
  Counter counter{5};

  // STATIC_REQUIRE(noexcept(counter | multiply_u(4)));
  REQUIRE((counter | multiply_u(4)) == 20);
}

TEST_CASE("forwards mutable objects to member functions") {
  Counter counter{5};

  counter | increment_u(2);

  REQUIRE(counter.value == 7);
}

constexpr auto value_u = UFCS(value);

TEST_CASE("accesses properties and preserves references") {
  Property property{};

  // STATIC_REQUIRE(std::is_same_v<decltype(property | value_u), int &>);
  (property | value_u) = 99;

  REQUIRE(property.value == 99);
}
