// 官方四接口与引擎分派。根据初始化时的网格规模固定选择主引擎或极小规模引擎，读取布局不改变状态。
// Included in fixed order by solution.cpp.

namespace engine_dispatch {
bool eng = false;
}
void init(int N, const std::vector<std::pair<int, int> > &services) {
    engine_dispatch::eng = N <= TE_NTA || (N >= TE_NTB && N <= TE_NT);
    if (engine_dispatch::eng)
        tiny_search::eInit(N, services);
    else
        initializeMainEngine(N, services);
}
void apply_add(int id, int count) {
    if (engine_dispatch::eng)
        tiny_search::eAdd(id, count);
    else
        addWithMainEngine(id, count);
}
void apply_remove(int id, int count) {
    if (engine_dispatch::eng)
        tiny_search::eRemove(id, count);
    else
        removeWithMainEngine(id, count);
}
const std::vector<int> &grid() {
    if (engine_dispatch::eng)
        return tiny_search::publicGrid;
    return mainEngineGrid();
}
