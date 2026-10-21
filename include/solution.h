// Official v2 online interface. The grader owns input/output and main().
// Working indices describe the current layout; no operation sequence is stored.
#pragma once
#include <utility>
#include <vector>

void init(int N, const std::vector<std::pair<int, int>>& services);
void apply_add(int id, int count);
void apply_remove(int id, int count);
const std::vector<int>& grid();
