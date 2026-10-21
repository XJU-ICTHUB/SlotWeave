#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
mkdir -p build
"${CXX:-c++}" -std=c++11 -O2 -Iinclude -c src/solution.cpp -o build/solution.o
"${CXX:-c++}" -std=c++11 -O2 -Iinclude tools/runner.cpp build/solution.o -o build/timeslot_runner
"${CXX:-c++}" -std=c++11 -O2 -Iinclude tests/test_interface.cpp build/solution.o -o build/timeslot_interface_tests
echo 'Built full engine, runner and interface tests in build/'
