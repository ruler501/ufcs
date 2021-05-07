#include <functional>
#include <tuple>
#include <type_traits>

#define FWD(x) static_cast<decltype(x)&&>(x)

template <typename T>
struct Ref {
  T&& ref;
};

#define UFCS(...) \
  ([](){\
    constexpr auto curried = []<typename... Args>(Args&&... args) constexpr {\
      constexpr auto apply_member_lambda = []<typename T, typename Tuple, std::size_t... indices>\
        (T&& t, std::index_sequence<indices...>, Tuple&& args)\
        noexcept(noexcept(FWD(t).__VA_ARGS__(FWD(std::get<indices>(FWD(args)).ref)...))) -> decltype(auto) {\
          return FWD(t).__VA_ARGS__(FWD(std::get<indices>(FWD(args)).ref)...);\
      };\
      constexpr auto apply_free_lambda = []<typename T, typename Tuple, std::size_t... indices>\
        (T&& t, std::index_sequence<indices...>, Tuple&& args)\
        noexcept(noexcept(__VA_ARGS__(FWD(t), FWD(std::get<indices>(FWD(args)).ref)...))) -> decltype(auto) {\
          return __VA_ARGS__(FWD(t), FWD(std::get<indices>(FWD(args)).ref)...);\
      };\
      constexpr auto has_member_lambda = []<typename T>\
        (T&&) {\
          if constexpr(requires (T&& t, Args&&... as) { FWD(t).__VA_ARGS__(FWD(as)...); }) return std::true_type{};\
          else return std::false_type{};\
      };\
      constexpr auto has_free_lambda = []<typename T>\
        (T&&) {\
          if constexpr(requires (T&& t, Args&&... as) { __VA_ARGS__(FWD(t), FWD(as)...); }) return std::true_type{};\
          else return std::false_type{};\
      };\
      struct ufcs_inner2 {\
        using args_tuple = std::tuple<Ref<Args>...>;\
        using apply_member_type = decltype(apply_member_lambda);\
        using apply_free_type = decltype(apply_free_lambda);\
        using has_member = decltype(has_member_lambda);\
        using has_free = decltype(has_free_lambda);\
        std::tuple<Ref<Args>...> _args;\
        decltype(apply_member_lambda) apply_member; \
        decltype(apply_free_lambda) apply_free;\
      };\
      return ufcs_inner2{Ref<Args>{FWD(args)}...};\
    };\
    using curried_type = decltype(curried);\
    constexpr auto apply_member_lambda = []<typename T>(T&& t)\
        noexcept(noexcept(FWD(t).__VA_ARGS__())) -> decltype(auto) { return FWD(t).__VA_ARGS__(); };\
    constexpr auto apply_free_lambda = []<typename T>(T&& t)\
        noexcept(noexcept(__VA_ARGS__(FWD(t)))) -> decltype(auto) { return __VA_ARGS__(FWD(t)); };\
    constexpr auto access_member_lambda = []<typename T>(T&& t)\
        noexcept -> decltype(std::invoke(&std::remove_reference_t<T>::__VA_ARGS__, FWD(t)))\
        { return t.__VA_ARGS__; };\
    constexpr auto has_member_lambda = []<typename T>(T&&) {\
        if constexpr(requires (T&& t) { FWD(t).__VA_ARGS__(); }) return std::true_type{};\
        else return std::false_type{};\
    };\
    constexpr auto has_free_lambda = []<typename T>(T&&) {\
        if constexpr(requires (T&& t) { __VA_ARGS__(FWD(t)); }) return std::true_type{};\
        else return std::false_type{};\
    };\
    constexpr auto has_property_lambda = []<typename T>(T&&) {\
        if constexpr(requires (T&& t) { FWD(t).__VA_ARGS__; }) return std::true_type{};\
        else return std::false_type{};\
    };\
    struct ufcs_inner : curried_type {\
        using apply_member_type = decltype(apply_member_lambda);\
        using apply_free_type = decltype(apply_free_lambda);\
        using access_member_type = decltype(access_member_lambda);\
        using has_member = decltype(has_member_lambda);\
        using has_free = decltype(has_free_lambda);\
        using has_property = decltype(has_property_lambda);\
        decltype(apply_member_lambda) apply_member;\
        decltype(apply_free_lambda) apply_free;\
        decltype(access_member_lambda) access_member;\
    };\
    return ufcs_inner{};\
  })()

template <typename Inner>
concept has_args = requires (Inner&& inner) { FWD(inner)._args; };

template<typename T, has_args Inner>
    requires std::is_invocable_r_v<std::true_type, typename std::remove_reference_t<Inner>::has_member, T>
constexpr decltype(auto) operator|(T&& t, Inner&& inner)
        noexcept(noexcept(FWD(inner).apply_member(FWD(t),
            std::make_index_sequence<std::tuple_size_v<typename std::remove_reference_t<Inner>::args_tuple>>{},
            FWD(inner._args)))) {
    return FWD(inner).apply_member(FWD(t),
        std::make_index_sequence<std::tuple_size_v<typename std::remove_reference_t<Inner>::args_tuple>>{},
        FWD(inner._args));
}

template<typename T, typename Inner>
    requires std::is_invocable_r_v<std::true_type, typename std::remove_reference_t<Inner>::has_member, T>
    && (!has_args<Inner>)
constexpr decltype(auto) operator|(T&& t, Inner&& inner)
        noexcept(noexcept(FWD(inner).apply_member(FWD(t)))) {
    return FWD(inner).apply_member(FWD(t));
}

template<typename T, has_args Inner>
    requires std::is_invocable_r_v<std::true_type, typename std::remove_reference_t<Inner>::has_free, T>
constexpr decltype(auto) operator|(T&& t, Inner&& inner)
        noexcept(noexcept(FWD(inner).apply_free(FWD(t),
            std::make_index_sequence<std::tuple_size_v<typename std::remove_reference_t<Inner>::args_tuple>>{},
            FWD(inner._args)))) {
    return FWD(inner).apply_free(FWD(t),
        std::make_index_sequence<std::tuple_size_v<typename std::remove_reference_t<Inner>::args_tuple>>{},
        FWD(inner._args)); }

template<typename T, typename Inner>
    requires std::is_invocable_r_v<std::true_type, typename std::remove_reference_t<Inner>::has_free, T>
    && (!has_args<Inner>)
constexpr decltype(auto) operator|(T&& t, Inner&& inner)
        noexcept(noexcept(FWD(inner).apply_free(FWD(t)))) {
    return FWD(inner).apply_free(FWD(t));
}

template<typename T, typename Inner>
    requires std::is_invocable_r_v<std::true_type, typename std::remove_reference_t<Inner>::has_property, T>
    && std::is_invocable_r_v<std::false_type, typename std::remove_reference_t<Inner>::has_member, T>
constexpr decltype(auto) operator|(T&& t, Inner&& inner) noexcept {
    return FWD(inner).access_member(FWD(t));
}