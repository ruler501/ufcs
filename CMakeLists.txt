cmake_minimum_required(VERSION 4.4)
project(ufcs LANGUAGES CXX)

option(UFCS_BUILD_TESTS "Build the UFCS tests" OFF)
set(CATCH2_INCLUDE_DIRS)

if(UFCS_BUILD_TESTS)
  find_package(Catch2 3 REQUIRED)

  include(CTest)
  include(Catch)

  set(CATCH2_INCLUDE_DIRS ${Catch2_ROOT}/include)
  add_executable(ufcs-tests tests/ufcs_tests.cpp)
  target_link_libraries(ufcs-tests PRIVATE Catch2::Catch2WithMain ufcs::ufcs)
  catch_discover_tests(ufcs-tests)
  set_target_properties(ufcs-tests PROPERTIES CXX_SCAN_FOR_MODULES OFF)
endif()

find_program(CLANG_TIDY_EXECUTABLE NAMES clang-tidy)
if(CLANG_TIDY_EXECUTABLE)
  set(CLANG_TIDY_HEADER_ARGS -std=c++23 -x c++)
  set(CMAKE_CXX_CLANG_TIDY "${CLANG_TIDY_EXECUTABLE}")
  foreach(include_dir IN LISTS CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES CATCH2_INCLUDE_DIRS)
    list(APPEND CLANG_TIDY_HEADER_ARGS "-isystem${include_dir}")
  endforeach()
  add_custom_target(clang-tidy
    COMMAND "${CLANG_TIDY_EXECUTABLE}"
      "${CMAKE_CURRENT_SOURCE_DIR}/ufcs.hpp"
      "${CMAKE_CURRENT_SOURCE_DIR}/tests/ufcs_tests.cpp" --
      ${CLANG_TIDY_HEADER_ARGS}
      -I${CMAKE_CURRENT_SOURCE_DIR}
    VERBATIM
  )
endif()

find_program(INCLUDE_WHAT_YOU_USE_EXECUTABLE NAMES include-what-you-use)
if(INCLUDE_WHAT_YOU_USE_EXECUTABLE)
  set(IWYU_HEADER_ARGS -std=c++23 -x c++)
  foreach(include_dir IN LISTS CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES CATCH2_INCLUDE_DIRS)
    list(APPEND IWYU_HEADER_ARGS "-isystem${include_dir}")
  endforeach()
  set(IWYU_SELF_ARGS_RAW --error --experimental=clang_mappings)
  set(IWYU_SELF_ARGS "")
  foreach(arg IN LISTS IWYU_SELF_ARGS_RAW)
    list(APPEND IWYU_SELF_ARGS "-Xiwyu" "${arg}")
  endforeach()
  MESSAGE(STATUS "IWYU_SELF_ARGS: ${IWYU_SELF_ARGS}")
  add_custom_target(include-what-you-use
    COMMAND "${INCLUDE_WHAT_YOU_USE_EXECUTABLE}" ${IWYU_SELF_ARGS} ${IWYU_HEADER_ARGS}
      "${CMAKE_CURRENT_SOURCE_DIR}/ufcs.hpp"
      "${CMAKE_CURRENT_SOURCE_DIR}/tests/ufcs_tests.cpp"
    VERBATIM
  )
endif()

find_program(CLANG_FORMAT_EXECUTABLE NAMES clang-format)
if(CLANG_FORMAT_EXECUTABLE)
  add_custom_target(clang-format
    COMMAND "${CLANG_FORMAT_EXECUTABLE}" -i
      "${CMAKE_CURRENT_SOURCE_DIR}/ufcs.hpp"
      "${CMAKE_CURRENT_SOURCE_DIR}/tests/ufcs_tests.cpp"
    VERBATIM
  )
endif()

add_library(ufcs INTERFACE)
add_library(ufcs::ufcs ALIAS ufcs)

target_compile_features(ufcs INTERFACE cxx_std_23)
target_include_directories(ufcs INTERFACE
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
  $<INSTALL_INTERFACE:include>
)
set_target_properties(ufcs PROPERTIES CXX_SCAN_FOR_MODULES OFF)