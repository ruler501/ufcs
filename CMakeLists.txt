cmake_minimum_required(VERSION 3.14)
project(ufcs LANGUAGES CXX)

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