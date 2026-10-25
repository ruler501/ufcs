#include <cstddef>     // for size_t
#include <functional>  // IWYU pragma: keep
#include <tuple>       // for tuple_size_v
#include <type_traits> // for remove_reference_t, is_invocable_r_v, true_type
#include <utility>     // for make_index_sequence

#define FWD(x) static_cast<decltype(x) &&>(x)

template <typename T> struct Ref {
  T &&ref;
};

template <typename Factory, typename... Args> struct curriable {
  using factory_type = Factory;
  using args_type = std::tuple<Ref<Args>...>;
  using args_tuple = std::tuple<Args...>;

  factory_type _factory;
  args_type _args;

  template <typename... NewArgs>
  auto operator()(NewArgs &&...newArgs)
    requires(sizeof...(NewArgs) > 0)
  {
    return [&]<std::size_t... indices>(std::index_sequence<indices...>) {
      return _factory(FWD(std::get<indices>(_args).ref)..., FWD(newArgs)...);
    }(std::make_index_sequence<std::tuple_size_v<args_type>>{});
  }

  explicit constexpr curriable(Factory f) noexcept
    requires(sizeof...(Args) == 0)
      : _factory(f), _args{} {}
  explicit curriable(Factory f, Args &&...args)
    requires(sizeof...(Args) > 0)
      : _factory(f), _args(Ref<Args>{FWD(args)}...) {}
};

template <typename Factory, typename... Args> curriable(Factory f, Args &&...args) -> curriable<Factory, Args...>;

#define UFCS(...)                                                                                                      \
  ([]<typename Self, typename... Args>(this Self self, Args &&...args) constexpr {                                     \
    constexpr auto apply_member_lambda =                                                                               \
        []<typename T, typename Tuple, std::size_t... indices>(                                                        \
            T &&t, std::index_sequence<indices...>,                                                                    \
            Tuple &&args) noexcept(noexcept(FWD(t).__VA_ARGS__(FWD(std::get<indices>(FWD(args)).ref)...)))             \
        -> decltype(auto) { return FWD(t).__VA_ARGS__(FWD(std::get<indices>(FWD(args)).ref)...); };                    \
    constexpr auto apply_free_lambda =                                                                                 \
        []<typename T, typename Tuple, std::size_t... indices>(                                                        \
            T &&t, std::index_sequence<indices...>,                                                                    \
            Tuple &&args) noexcept(noexcept(__VA_ARGS__(FWD(t), FWD(std::get<indices>(FWD(args)).ref)...)))            \
        -> decltype(auto) { return __VA_ARGS__(FWD(t), FWD(std::get<indices>(FWD(args)).ref)...); };                   \
    constexpr auto access_member_lambda =                                                                              \
        []<typename T>(T &&t) noexcept -> decltype(std::invoke(&std::remove_reference_t<T>::__VA_ARGS__, FWD(t))) {    \
      return t.__VA_ARGS__;                                                                                            \
    };                                                                                                                 \
    constexpr auto has_member_lambda = []<typename T>(T &&) {                                                          \
      if constexpr (requires(T &&t, Args &&...as) { FWD(t).__VA_ARGS__(FWD(as)...); }) {                               \
        return std::true_type{};                                                                                       \
      } else {                                                                                                         \
        return std::false_type{};                                                                                      \
      }                                                                                                                \
    };                                                                                                                 \
    constexpr auto has_free_lambda = []<typename T>(T &&) {                                                            \
      if constexpr (requires(T &&t, Args &&...as) { __VA_ARGS__(FWD(t), FWD(as)...); }) {                              \
        return std::true_type{};                                                                                       \
      } else {                                                                                                         \
        return std::false_type{};                                                                                      \
      }                                                                                                                \
    };                                                                                                                 \
    constexpr auto has_property_lambda = []<typename T>(T &&) {                                                        \
      if constexpr (requires(T &&t) { FWD(t).__VA_ARGS__; }) {                                                         \
        return std::true_type{};                                                                                       \
      } else {                                                                                                         \
        return std::false_type{};                                                                                      \
      }                                                                                                                \
    };                                                                                                                 \
    struct ufcs_inner : public curriable<std::remove_cvref_t<Self>, Args...> {                                         \
      using apply_member_type = decltype(apply_member_lambda);                                                         \
      using apply_free_type = decltype(apply_free_lambda);                                                             \
      using access_member_type = decltype(access_member_lambda);                                                       \
      using has_member = decltype(has_member_lambda);                                                                  \
      using has_free = decltype(has_free_lambda);                                                                      \
      using has_property = decltype(has_property_lambda);                                                              \
      apply_member_type apply_member;                                                                                  \
      apply_free_type apply_free;                                                                                      \
      access_member_type access_member;                                                                                \
      explicit constexpr ufcs_inner(Self self, apply_member_type am, apply_free_type af, access_member_type ac,        \
                                    Args &&...as) noexcept(sizeof...(Args) == 0)                                       \
          : ufcs_inner::curriable(self, FWD(as)...), apply_member(am), apply_free(af), access_member(ac) {}            \
      using curriable<std::remove_cvref_t<Self>, Args...>::operator();                                                 \
    };                                                                                                                 \
    return ufcs_inner{self, apply_member_lambda, apply_free_lambda, access_member_lambda, FWD(args)...};               \
  })()

template <typename Inner>
concept is_ufcs = requires(Inner &&inner) {
  typename std::remove_reference_t<Inner>::apply_member_type;
  typename std::remove_reference_t<Inner>::apply_free_type;
  typename std::remove_reference_t<Inner>::access_member_type;
  typename std::remove_reference_t<Inner>::factory_type;
  typename std::remove_reference_t<Inner>::args_type;
};

template <typename T, is_ufcs Inner>
  requires std::is_invocable_r_v<std::true_type, typename std::remove_reference_t<Inner>::has_member, T>
constexpr decltype(auto) operator|(T &&t, Inner &&inner) noexcept(noexcept(FWD(inner).apply_member(
    FWD(t), std::make_index_sequence<std::tuple_size_v<typename std::remove_reference_t<Inner>::args_tuple>>{},
    FWD(inner)._args))) {
  return FWD(inner).apply_member(
      FWD(t), std::make_index_sequence<std::tuple_size_v<typename std::remove_reference_t<Inner>::args_tuple>>{},
      FWD(inner)._args);
}

template <typename T, is_ufcs Inner>
  requires std::is_invocable_r_v<std::true_type, typename std::remove_reference_t<Inner>::has_free, T>
constexpr decltype(auto) operator|(T &&t, Inner &&inner) noexcept(noexcept(FWD(inner).apply_free(
    FWD(t), std::make_index_sequence<std::tuple_size_v<typename std::remove_reference_t<Inner>::args_tuple>>{},
    FWD(inner)._args))) {
  return FWD(inner).apply_free(
      FWD(t), std::make_index_sequence<std::tuple_size_v<typename std::remove_reference_t<Inner>::args_tuple>>{},
      FWD(inner)._args);
}

template <typename T, typename Inner>
  requires std::is_invocable_v<std::true_type, Inner, T> && (!is_ufcs<Inner>)
constexpr decltype(auto) operator|(T &&t, Inner &&inner) noexcept(noexcept(FWD(inner).apply_free(FWD(t)))) {
  return FWD(inner)(FWD(t));
}

template <typename T, is_ufcs Inner>
  requires std::is_invocable_r_v<std::true_type, typename std::remove_reference_t<Inner>::has_property, T> &&
           std::is_invocable_r_v<std::false_type, typename std::remove_reference_t<Inner>::has_member, T>
constexpr decltype(auto) operator|(T &&t, Inner &&inner) noexcept {
  return FWD(inner).access_member(FWD(t));
}