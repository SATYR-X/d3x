#include "dp_manager.h"
// DpManager 类负责动态规划中的计数管理，优化覆盖与取消覆盖的计算过程

using namespace std;

// DpManager类的构造函数实现。
// 初始化动态规划管理器，设置节点向量和变量数量。
DpManager::DpManager(const vector<Node> &nodes, const int num_var)
    : num_var_(num_var),
      table_elems_(nodes.size()),
      var_heads_(num_var, 0),
      num_elems_(num_var, 0),
      diff_counter_(nodes.size(), 0),
      diff_counter_hi_(nodes.size(), 0),
      entries_counter_(0) {
    // 初始化优先队列，用于管理变量的上下方向顺序。
    upper_varorder_pq_ = priority_queue<uint16_t>();
    lower_varorder_pq_ = priority_queue<uint16_t, vector<uint16_t>, greater<uint16_t>>();

    int previous_var = -1;

    for (size_t i = 0; i < nodes.size(); i++) {
        const Node &node = nodes[i];
        if (node.var != previous_var) {
            var_heads_[node.var] = i;
            previous_var = node.var;
        }
    }
}
