#include "solution.h"
#include <algorithm>
#include <iostream>
#include <map>
#include <stdexcept>
#include <vector>

std::map<int, int> counts() {
    std::map<int, int> result;
    for (int id : grid()) ++result[id];
    return result;
}

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}

int main() {
    try {
        const std::vector<std::pair<int, int>> services = {{42, 3}, {1000000007, 2}};
        init(17, services);
        const auto initial = grid();
        require(initial.size() == 17 && counts()[0] == 12, "init counts");
        apply_add(17, 4);
        const auto first = grid();
        require(counts()[17] == 4 && counts()[0] == 8, "add counts");
        require(grid() == first && grid() == first, "repeated getter");
        apply_remove(42, 100);
        require(counts()[42] == 0 && counts()[0] == 11, "remove clamp");
        apply_add(-7, 100);
        require(counts()[-7] == 11 && counts()[0] == 0, "add clamp and sparse id");
        init(1, {});
        require(grid().size() == 1 && counts()[0] == 1, "reset to smaller grid");
        apply_add(9, 1);
        require(grid()[0] == 9, "N equals K add");
        apply_remove(9, 1);
        require(grid()[0] == 0, "N equals K remove");
        init(17, services);
        require(grid() == initial, "init reproducibility");
        apply_add(17, 4);
        require(grid() == first, "init resets complete engine state");
        std::cout << "PASS: public API, reset, repeated reads, clamps and sparse IDs\n";
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
