cmake_minimum_required(VERSION 3.16)
project(fixed_timeslot_uniformity LANGUAGES CXX)

# Implementation fragments are intentionally compiled together. This preserves
# cross-module inlining and the original macro/state lifetime.
add_library(timeslot STATIC src/solution.cpp)
target_include_directories(timeslot PUBLIC include)
target_compile_features(timeslot PUBLIC cxx_std_11)
set_target_properties(timeslot PROPERTIES CXX_EXTENSIONS OFF)

add_executable(timeslot_runner tools/runner.cpp)
target_link_libraries(timeslot_runner PRIVATE timeslot)
add_executable(timeslot_interface_tests tests/test_interface.cpp)
target_link_libraries(timeslot_interface_tests PRIVATE timeslot)

option(ENABLE_SANITIZERS "Enable AddressSanitizer and UndefinedBehaviorSanitizer" OFF)
if(ENABLE_SANITIZERS)
  foreach(target timeslot timeslot_runner timeslot_interface_tests)
    target_compile_options(${target} PRIVATE -fsanitize=address,undefined -fno-omit-frame-pointer)
  endforeach()
  foreach(target timeslot_runner timeslot_interface_tests)
    target_link_options(${target} PRIVATE -fsanitize=address,undefined)
  endforeach()
endif()

enable_testing()
add_test(NAME interface_reset COMMAND timeslot_interface_tests)
find_package(Python3 COMPONENTS Interpreter)
if(Python3_Interpreter_FOUND)
  add_test(NAME solver_properties COMMAND ${Python3_EXECUTABLE}
    ${CMAKE_CURRENT_SOURCE_DIR}/tools/verify.py --runner $<TARGET_FILE:timeslot_runner>)
  add_test(NAME own_arithmetic COMMAND ${Python3_EXECUTABLE}
    ${CMAKE_CURRENT_SOURCE_DIR}/tools/check_solution.py)
endif()
