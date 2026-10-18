cmake_minimum_required(VERSION 3.14)
project(ufcs LANGUAGES CXX)

find_program(CLANG_TIDY_EXECUTABLE NAMES clang-tidy)
if(CLANG_TIDY_EXECUTABLE)
  set(CMAKE_CXX_CLANG_TIDY "${CLANG_TIDY_EXECUTABLE}")
  set(CLANG_TIDY_HEADER_ARGS -std=c++23 -x c++)
  foreach(include_dir IN LISTS CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES)
    list(APPEND CLANG_TIDY_HEADER_ARGS "-isystem${include_dir}")
  endforeach()
  add_custom_target(clang-tidy
    COMMAND "${CLANG_TIDY_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/ufcs.hpp" --
      ${CLANG_TIDY_HEADER_ARGS}
    VERBATIM
  )
endif()

find_program(CLANG_FORMAT_EXECUTABLE NAMES clang-format)
if(CLANG_FORMAT_EXECUTABLE)
  add_custom_target(clang-format
    COMMAND "${CLANG_FORMAT_EXECUTABLE}" -i "${CMAKE_CURRENT_SOURCE_DIR}/ufcs.hpp"
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

include(GNUInstallDirs)
install(TARGETS ufcs EXPORT ufcsTargets)
install(FILES ufcs.hpp DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
install(EXPORT ufcsTargets
  FILE ufcsTargets.cmake
  NAMESPACE ufcs::
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/ufcs
)