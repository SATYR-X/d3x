#ifndef DP_MANAGER_H_
#define DP_MANAGER_H_

#include <memory>
#include <queue>
#include <vector>

#include "dancing_on_zdd.h"

/**
 * DpManager类用于管理覆盖/取消覆盖操作的动态规划表。
 * 该类存储了处理过的节点单元ID的顺序，并在执行覆盖/取消覆盖操作时反转顺序。
 */
class DpManager {
   public:
    /**
     * 构造函数，初始化动态规划管理器。
     * @param nodes 节点的向量引用。
     * @param num_var 变量的数量。
     */
    DpManager(const std::vector<Node> &nodes, const int num_var);

    // 禁用拷贝构造函数，防止对象被复制。
    DpManager(const DpManager &obj) = delete;

    /**
     * 增加节点的差异计数。
     * @param var 变量编号。
     * @param node_id 节点ID。
     * @param count 增加的计数。
     * 如果节点的差异计数大于0，则不进行操作。
     * 否则，更新表格元素并将变量加入优先队列。
     */
    void add_node_diff_count(uint16_t var, int32_t node_id, count_t count) {
        diff_counter_[node_id] += count;
        if (diff_counter_[node_id] > count) {
            return;
        }

        auto var_num_elems = num_elems_[var];
        num_elems_[var]++;
        table_elems_[var_heads_[var] + var_num_elems] = node_id;
        if (!var_num_elems) {
            lower_varorder_pq_.push(var);
        }
    }

    /**
     * 增加节点的高分支差异计数。
     * @param var 变量编号。
     * @param node_id 节点ID。
     * @param count 增加的计数。
     * 如果节点的差异计数或高分支差异计数大于0，则只增加高分支差异计数。
     * 否则，更新表格元素并将变量加入优先队列。
     */
    void add_node_diff_count_high(uint16_t var, int32_t node_id,
                                  count_t count) {
        if (diff_counter_[node_id] > 0 || diff_counter_hi_[node_id] > 0) {
            diff_counter_hi_[node_id] += count;
            return;
        }

        diff_counter_hi_[node_id] += count;
        table_elems_[var_heads_[var] + num_elems_[var]] = node_id;
        num_elems_[var]++;
        if (num_elems_[var] == 1) {
            upper_varorder_pq_.push(var);
        }
    }

    /**
     * 增加节点的低分支差异计数。
     * @param var 变量编号。
     * @param node_id 节点ID。
     * @param count 增加的计数。
     * 如果节点的差异计数或高分支差异计数大于0，则只增加差异计数。
     * 否则，更新表格元素并将变量加入优先队列。
     */
    void add_node_diff_count_low(uint16_t var, int32_t node_id, count_t count) {
        if (diff_counter_[node_id] > 0 || diff_counter_hi_[node_id] > 0) {
            diff_counter_[node_id] += count;
            return;
        }

        diff_counter_[node_id] += count;
        table_elems_[var_heads_[var] + num_elems_[var]] = node_id;
        num_elems_[var]++;
        if (num_elems_[var] == 1) {
            upper_varorder_pq_.push(var);
        }
    }

    /**
     * 获取指定变量和索引的节点ID。
     * @param var 变量编号。
     * @param i 索引。
     * @return 节点ID。
     */
    inline int32_t at(uint16_t var, int32_t i) const noexcept {
        return table_elems_[var_heads_[var] + i];
    }

    /**
     * 获取指定变量的元素数量。
     * @param var 变量编号。
     * @return 元素数量。
     */
    int32_t num_elems(uint16_t var) const { return num_elems_[var]; }

    /**
     * 获取指定节点的差异计数。
     * @param node_id 节点ID。
     * @return 差异计数。
     */
    count_t count_at(int32_t node_id) const { return diff_counter_[node_id]; }

    /**
     * 获取指定节点的低分支差异计数。
     * @param node_id 节点ID。
     * @return 低分支差异计数。
     */
    count_t low_count_at(int32_t node_id) const {
        return diff_counter_[node_id];
    }

    /**
     * 获取指定节点的高分支差异计数。
     * @param node_id 节点ID。
     * @return 高分支差异计数。
     */
    count_t high_count_at(int32_t node_id) const {
        return diff_counter_hi_[node_id];
    }

    /**
     * 获取并清除指定节点的差异计数。
     * @param node_id 节点ID。
     * @return 差异计数。
     */
    count_t get_count_and_clear(const int32_t node_id) {
        auto c = diff_counter_[node_id];
        diff_counter_[node_id] = 0;
        return c;
    }

    /**
     * 获取并清除指定节点的低分支差异计数。
     * @param node_id 节点ID。
     * @return 低分支差异计数。
     */
    count_t get_low_count_and_clear(const int32_t node_id) {
        auto c = diff_counter_[node_id];
        diff_counter_[node_id] = 0;
        return c;
    }

    /**
     * 获取并清除指定节点的高分支差异计数。
     * @param node_id 节点ID。
     * @return 高分支差异计数。
     */
    count_t get_high_count_and_clear(const int32_t node_id) {
        auto c = diff_counter_hi_[node_id];
        diff_counter_hi_[node_id] = 0;
        return c;
    }

    /**
     * 清除指定变量的计数器。
     * @param var 变量编号。
     */
    void clear_var_counter(uint16_t var) { num_elems_[var] = 0; }

    /**
     * 清除指定变量的元素。
     * @param var 变量编号。
     * 清除与该变量相关的所有节点的差异计数。
     */
    void clear_var_elems(uint16_t var) {
        for (size_t i = 0; i < num_elems_[var]; i++) {
            auto node_id = at(var, i);
            diff_counter_[node_id] = 0UL;
            diff_counter_hi_[node_id] = 0UL;
        }
        num_elems_[var] = 0;
    }

    /**
     * 获取上方向非零变量。
     * @return 非零变量编号。
     * 如果优先队列为空，则返回0。
     */
    uint16_t upper_nonzero_var() {
        if (upper_varorder_pq_.empty()) return 0;

        uint16_t next = upper_varorder_pq_.top();
        upper_varorder_pq_.pop();
        return next;
    }

    /**
     * 获取下方向非零变量。
     * @return 非零变量编号。
     * 如果优先队列为空，则返回0。
     */
    uint16_t lower_nonzero_var() {
        if (lower_varorder_pq_.empty()) return 0;

        uint16_t next = lower_varorder_pq_.top();
        lower_varorder_pq_.pop();
        return next;
    }

    /**
     * 将变量加入上方向优先队列。
     * @param var 变量编号。
     */
    void add_upper_var(uint16_t var) { upper_varorder_pq_.push(var); }

    /**
     * 将变量加入下方向优先队列。
     * @param var 变量编号。
     */
    void add_lower_var(uint16_t var) { lower_varorder_pq_.push(var); }

   private:
    // 存储表格元素的向量
    std::vector<int32_t> table_elems_;

    // 存储变量头部索引的向量
    std::vector<int32_t> var_heads_;

    // 存储每个变量元素数量的向量
    std::vector<int32_t> num_elems_;

    // 存储节点差异计数的向量
    std::vector<count_t> diff_counter_;

    // 存储节点高分支差异计数的向量
    std::vector<count_t> diff_counter_hi_;

    // 记录条目计数器
    uint32_t entries_counter_;

    // 变量数量
    const uint16_t num_var_;

    // 变量缓存
    int var_cache_;

    // 下方向优先队列，按升序排列
    std::priority_queue<uint16_t, std::vector<uint16_t>, std::greater<uint16_t>> lower_varorder_pq_;

    // 上方向优先队列，按降序排列
    std::priority_queue<uint16_t> upper_varorder_pq_;
};

#endif  // DP_MANAGER_H_