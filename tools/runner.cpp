// Local evaluator only. The arithmetic and I/O restrictions apply to solution.cpp.
#include "solution.h"
#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
using Clock = std::chrono::steady_clock;

std::map<int, int> histogram(const std::vector<int>& layout) {
    std::map<int, int> counts;
    for (int id : layout) ++counts[id];
    return counts;
}

void validate(const std::vector<int>& layout, int n, std::map<int, int> expected) {
    if (static_cast<int>(layout.size()) != n) throw std::runtime_error("wrong grid size");
    const auto actual = histogram(layout);
    for (const auto& entry : actual) {
        if (expected[entry.first] != entry.second) throw std::runtime_error("wrong type count");
    }
    for (const auto& entry : expected) {
        auto it = actual.find(entry.first);
        if (entry.second != (it == actual.end() ? 0 : it->second)) {
            throw std::runtime_error("missing type");
        }
    }
}

double uniformity(const std::vector<int>& layout) {
    const int n = static_cast<int>(layout.size());
    std::map<int, std::vector<int>> positions;
    for (int i = 0; i < n; ++i) positions[layout[i]].push_back(i);
    double result = 0;
    for (const auto& entry : positions) {
        const auto& p = entry.second;
        const int s = static_cast<int>(p.size());
        double u = 1;
        if (s > 1 && s < n) {
            // Integer numerator avoids rounding the ideal gap separately.
            long long deviation = 0;
            for (int i = 0; i < s; ++i) {
                const int next = i + 1 == s ? p[0] + n : p[i + 1];
                deviation += std::abs(1LL * s * (next - p[i]) - n);
            }
            const long long worst = 2LL * (s - 1) * (n - s);
            u -= static_cast<double>(deviation) / static_cast<double>(worst);
        }
        result += static_cast<double>(s) / n * u;
    }
    return result;
}

void print_grid(const std::vector<int>& layout) {
    std::cout << '[';
    for (std::size_t i = 0; i < layout.size(); ++i) {
        if (i) std::cout << ',';
        std::cout << layout[i];
    }
    std::cout << ']';
}
} // namespace

int main(int argc, char** argv) {
    try {
        if (argc < 2 || argc > 3) throw std::runtime_error("usage: timeslot_runner INPUT [--trace]");
        const bool trace = argc == 3 && std::string(argv[2]) == "--trace";
        if (argc == 3 && !trace) throw std::runtime_error("unknown option");
        std::ifstream in(argv[1]);
        int n, m, q;
        if (!(in >> n >> m) || n < 1 || n > 10000 || m < 0) throw std::runtime_error("invalid header");
        std::vector<std::pair<int, int>> services;
        std::map<int, int> expected;
        int occupied = 0;
        for (int i = 0; i < m; ++i) {
            int id, count;
            if (!(in >> id >> count) || id == 0 || count < 0 || count > n - occupied) {
                throw std::runtime_error("invalid initial service");
            }
            services.push_back({id, count});
            expected[id] += count;
            occupied += count;
        }
        expected[0] = n - occupied;
        if (!(in >> q) || q < 1 || q > 1000) throw std::runtime_error("invalid operation count");
        struct Operation { int type, id, count; };
        std::vector<Operation> operations(q);
        for (auto& op : operations) {
            if (!(in >> op.type >> op.id >> op.count) || (op.type != 1 && op.type != 2)) {
                throw std::runtime_error("invalid operation");
            }
        }
        const auto begin = Clock::now();
        init(n, services);
        const auto initialized = Clock::now();
        validate(grid(), n, expected);
        const std::vector<int> initial = grid();
        std::vector<int> first_result;
        double sum_u = 0, sum_v = 0;
        long long operation_ns = 0;
        int extra_changed = 0;
        std::cout << std::setprecision(17);
        if (trace) { std::cout << "{\"initial\":"; print_grid(grid()); std::cout << ",\"steps\":["; }
        for (int step = 0; step < q; ++step) {
            const auto op = operations[step];
            const std::vector<int> previous = grid();
            const int request = std::max(0, op.count);
            const int k = op.id == 0 ? 0 : std::min(request, expected[op.type == 1 ? 0 : op.id]);
            if (op.id != 0) {
                expected[op.id] += op.type == 1 ? k : -k;
                expected[0] += op.type == 1 ? -k : k;
            }
            const auto t0 = Clock::now();
            if (op.type == 1) apply_add(op.id, op.count); else apply_remove(op.id, op.count);
            const auto& current = grid();
            const auto t1 = Clock::now();
            operation_ns += std::chrono::duration_cast<std::chrono::nanoseconds>(t1 - t0).count();
            validate(current, n, expected);
            const std::vector<int> snapshot = current;
            if (step == 0) first_result = snapshot;
            if (grid() != snapshot || grid() != snapshot) throw std::runtime_error("grid() changes state");
            int changed = 0;
            for (int i = 0; i < n; ++i) changed += previous[i] != current[i];
            if (changed < k || changed > n || (k == 0 && changed != 0)) {
                throw std::runtime_error("invalid change accounting");
            }
            const double u = uniformity(current);
            const double v = k == n ? 1 : 1 - static_cast<double>(changed - k) / (n - k);
            if (u < -1e-12 || u > 1 + 1e-12 || v < 0 || v > 1) throw std::runtime_error("score out of range");
            sum_u += u;
            sum_v += v;
            extra_changed += changed - k;
            if (trace) {
                if (step) std::cout << ',';
                std::cout << "{\"K\":" << k << ",\"M\":" << changed << ",\"U\":" << u << ",\"V\":" << v << ",\"grid\":";
                print_grid(current);
                std::cout << '}';
            }
        }
        const double mean_u = sum_u / q, mean_v = sum_v / q;
        // Reinitialization must erase the previous run's state.
        init(n, services);
        if (grid() != initial) throw std::runtime_error("init() is not reproducible");
        const auto first_op = operations.front();
        if (first_op.type == 1) apply_add(first_op.id, first_op.count);
        else apply_remove(first_op.id, first_op.count);
        if (grid() != first_result) throw std::runtime_error("init() did not reset operation state");
        if (trace) std::cout << "],\"summary\":";
        std::cout << "{\"N\":" << n << ",\"Q\":" << q << ",\"uniformity\":" << mean_u
                  << ",\"stability\":" << mean_v << ",\"quality\":" << 0.55 * mean_u + 0.35 * mean_v
                  << ",\"extra_changed_total\":" << extra_changed
                  << ",\"init_us\":" << std::chrono::duration<double, std::micro>(initialized - begin).count()
                  << ",\"operation_us\":" << static_cast<double>(operation_ns) / 1000 << '}';
        if (trace) std::cout << '}';
        std::cout << '\n';
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
