# Copilot instructions for ufcs

## Repository overview

This repository is a tiny, header-only C++23 utility library centered on `ufcs.hpp`. The primary public API is the `UFCS(...)` macro, which builds a callable object that dispatches to either a member function, a free function, or a property access based on the argument types and the available `requires` checks.

The project intentionally has almost no runtime code outside the header:

- `ufcs.hpp` contains the library implementation and the `operator|` overloads that drive dispatch.
- `CMakeLists.txt` defines an interface library target, install rules, and optional tooling targets for `clang-tidy`, `include-what-you-use`, and `clang-format`.
- `flake.nix` provides a reproducible C++ toolchain for this project.
- `.clang-format` and `.clang-tidy` define the repo's coding and static-analysis expectations.

There is no test suite or source tree beyond the single header; most validation is compile-time and header-focused.

## Build, lint, and validation commands

Use the repo-local dev shell when available:

```bash
nix develop
```

Then configure and build:

```bash
cmake -S . -B build
cmake --build build
```

Optional quality targets, if the tools are installed:

```bash
cmake --build build --target clang-tidy
cmake --build build --target include-what-you-use
cmake --build build --target clang-format
```

There is no dedicated automated test target in this repository. For one-off validation of a header change, compile a minimal translation unit against the project include path:

```bash
cat > /tmp/ufcs_check.cpp <<'EOF'
#include "ufcs.hpp"
#include <string>

struct S {
  std::string value() const { return "ok"; }
};

int main() {
  S s{};
  auto f = UFCS(value);
  return (s | f) == "ok" ? 0 : 1;
}
EOF
c++ -std=c++23 -I. /tmp/ufcs_check.cpp -o /tmp/ufcs_check
```

This is the closest equivalent to a "single test" in this repo.

## High-level architecture

The library is intentionally concentrated into one abstraction:

- `FWD(x)` is a forwarding helper used throughout the implementation.
- `Ref<T>` wraps arguments so the library can preserve reference semantics while building a callable object.
- `UFCS(...)` creates an object with `apply_member`, `apply_free`, and `access_member` lambdas plus `has_member`, `has_free`, and `has_property` trait objects.
- `operator|` performs overload resolution by checking whether the target object supports the requested member method, free function, or property access, then forwards the arguments and preserves `noexcept`/`decltype` behavior.

In practical terms, the library is a compile-time dispatch layer: it chooses the valid call form at compile time and leaves the run-time behavior to the underlying C++ call. This is why the most important code paths live in the same header, and why changes should be validated by exercising both member and free-function dispatch.

## Key conventions

- Keep changes in `ufcs.hpp` unless the build system itself must change.
- This project is C++23-only. Prefer `requires` clauses, `std::invoke`, `std::tuple`, and forwarding references instead of older pattern-based alternatives.
- Preserve the existing forwarding and trait machinery (`FWD`, `Ref<T>`, `has_args`, `operator|`) when editing dispatch behavior.
- Follow the style enforced by `.clang-format`: LLVM-based formatting with a 120-column width and 2-space indentation.
- Keep the library header-only and installable via CMake; avoid introducing new source files or runtime dependencies.
- When modifying dispatch logic, validate both member-function and free-function forms to ensure the overload checks still prefer the right branch.
- The generated `build/` directory is build output and should not be hand-edited.

## Practical guidance for future Copilot sessions

- Prefer surgical edits in `ufcs.hpp` and `CMakeLists.txt`; this repo is small enough that a single file often contains the relevant behavior.
- Any change to the macro or `operator|` logic should be checked with a minimal compile-based example, not just a full project build.
- When adding functionality, keep the API compatible with the existing template-heavy dispatch style rather than introducing a separate abstraction layer.
