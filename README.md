# SlotWeave：固定时隙均衡算法

华为算法挑战赛第39期实现。在线维护环形时隙表，结合链式DP、稳定性定价局部搜索和分层重建，平衡分布均匀度与布局改动成本。

- [算法说明](docs/solution.md)
- [源码入口](src/solution.cpp) · [接口定义](include/solution.h)
- 论坛题解：待发表

## 构建与运行

GCC/Clang，C++11；验证工具需要Python 3。

```sh
sh tools/build.sh
./build/timeslot_runner tests/data/example1.txt
python3 tools/verify.py --runner build/timeslot_runner
```

`src/solution.cpp` 顺序包含18个实现片段，`.inc` 文件不单独编译。需要单文件时运行 `python3 tools/amalgamate.py --out build/Solution.cpp`。

## 系列题解

[题解总目录](https://github.com/XJU-ICTHUB/Huawei-Algorithm-Challenge) · [第38期 MemWeave](https://github.com/XJU-ICTHUB/MemWeave) · [第38期论坛题解](https://bbs.huaweicloud.com/forum/thread-02127222761354471267-1-1.html)
