# SlotWeave：固定时隙均衡算法

Candyman的华为算法挑战赛第39期个人题解与完整通用引擎。这是比赛核心算法的可读整理版。保留强制放置的链式 DP、重叠最大化分层重建、稳定性定价局部搜索、多起点初始化和极小规模搜索，按模块解释它们如何组合。

代码按18个模块组织，配套数学推导、模块导航和复现工具，便于理解完整算法并验证修改。

作者团队报告的最终参赛成绩为 **0.85013665**。公开版从该工程的未拟合父本提取通用引擎，移除预存样例路径、输入哈希选种子和两条榜单后选参数。它没有独立官方分数；来源、整理边界和验证方法见 [来源说明](docs/provenance.md)。

## 建议阅读顺序

1. [完整中文题解](docs/solution.md)：评分建模、DP转移、重建及搜索策略。
2. [代码导读](docs/code-guide.md)：模块地图、推荐入口和状态变量词典。
3. [操作流水线](src/detail/11_operation_pipeline.inc)：从一次操作串起完整算法。
4. [链式放置 DP](src/detail/06_chain_dp.inc)与[重建层 DP](src/detail/08_rebuild_layers.inc)：阅读主要优化。
5. [验证记录](docs/results.md)：核对整理是否改变了通用引擎的行为。

## 保留的核心

| 组成 | 解决什么问题 |
|---|---|
| 环形同类链、类型/空位位图、增量代价缓存 | 快速查询与修改相邻间隔 |
| 带容量配额、服务与空位联合代价、链式 DP | 批量增加时协同选择多个位置 |
| 保留颗粒的晶格 DP、批量释放 | 批量删除时维护剩余服务的间隔 |
| 种子局搜、MN伙伴搜索、类型保序重排 | 在移动成本约束下修复局部缺陷 |
| OM分层重建、命中价值和keep-DP | 布局退化时重排，同时尽量保留旧位置 |
| 重建后的退款交换与空位修复 | 减少不必要移动、修复新产生的缺陷 |
| 多构造初始化、队列局搜、阈值接受 | 为在线过程构造更好的起点 |
| 小圆环的全对搜索和有预算分支定界 | 利用极小规模允许的更细搜索 |

规模档位、窗口、工作预算及固定伪随机流仍然保留，它们承担算法的性能分工。删去的是预存答案和针对榜单输入指纹的选择器，而不是所有启发式参数。它们不构成全局最优性保证。

## 构建与运行

支持 GCC/Clang，使用 C++11。内核使用编译器的位查询内建函数；自动测试还需要 Python 3。

```sh
sh tools/build.sh
./build/timeslot_interface_tests
python3 tools/check_solution.py
python3 tools/verify.py --runner build/timeslot_runner

./build/timeslot_runner tests/data/example1.txt
./build/timeslot_runner tests/data/example2.txt --trace
```

可用 `CXX=g++-16 sh tools/build.sh` 或 `CXX=clang++ sh tools/build.sh` 指定编译器。初次编译完整引擎比编译小型教学代码耗时更长。

也附有 CMake 3.16+ 配置：

```sh
cmake -S . -B build-cmake -DCMAKE_BUILD_TYPE=Release
cmake --build build-cmake -j2
ctest --test-dir build-cmake --output-on-failure
```

运行器输出 JSON。`quality` 是 `0.55×mean(U)+0.35×mean(V)`，不包含官方速度项；`operation_us` 和 `init_us` 是本机测量值。未知的官方参考耗时不能由本地工具补造。

## 目录与编译方式

```text
include/solution.h       官方 v2 四函数接口
src/solution.cpp         按原执行依赖顺序包含18个实现片段
src/detail/*.inc         配置、状态、放置、DP、重建、搜索与入口
docs/solution.md         数学模型与完整算法题解
docs/code-guide.md       代码阅读地图和符号解释
docs/provenance.md       通用版的来源及删改边界
docs/results.md          本次整理的验证结果
tools/                  构建、运行、静态检查、独立评分和单文件导出
tests/                  接口测试与样例输入
```

实现片段不是独立翻译单元。它们按原有声明、状态、内联和宏生命周期顺序组成一个翻译单元，以保持优化条件和调用顺序。不要把每个 `.inc` 单独编译。

需要单文件时可导出：

```sh
python3 tools/amalgamate.py --out build/Solution.cpp
```

导出文件以 `#include "solution.h"` 开头，接口与模块版一致；仓库不重复保存另一份数百KB的生成代码。

## 重要约定

- 空位0也参与均匀度；所有间隔包含圆环首尾。
- 增删首先满足数量约束，删除夹到现有数量，增加防御式夹到空位数。
- 改动成本相对本次操作入口记账，不是交换次数。当前状态索引和小型在线统计会保留，不储存未来操作或过去的布局序列。
- 求解器自己的计算保持加减、比较、位运算和移位；软件乘除、固定点数和位查询实现相应计算。
- 前瞻H、候选窗口、配额、代价权重和搜索预算都是启发式。它们不保证每步官方质量上升，也不保证全局最优。
- 本地评测器中的浮点、计时和输入输出不属于求解内核。

## 系列题解

[返回个人参赛题解总目录](https://github.com/XJU-ICTHUB/Huawei-Algorithm-Challenge)

| 期数 | 项目 | 题目与阅读入口 |
|---|---|---|
| 第38期 | [MemWeave](https://github.com/deafenken/MemWeave) | GPU显存约束调度：[论坛题解](https://bbs.huaweicloud.com/forum/thread-02127222761354471267-1-1.html) |
| 第39期 | SlotWeave | 固定时隙均衡：[完整题解](docs/solution.md)、[代码导读](docs/code-guide.md) |

