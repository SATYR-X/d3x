#ifndef DANCING_ON_ZDD_H_
#define DANCING_ON_ZDD_H_

#include <assert.h>
#include <limits.h>
#include <unistd.h>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <iterator>
#include <memory>
#include <queue>
#include <sstream>
#include <stack>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

#include "hidden_node_stack.h"
using namespace std;
// 前向声明，避免头文件之间的循环依赖
class DpManager;
class HiddenNodeStack;

/**
 * constants
 */
// 代表 ZDD 结构中的终端节点（1-terminal）
constexpr int DD_ONE_TERM =
    -1;  // represents the $\top$-terminal node of DanceDD.
// 代表 ZDD 结构中的终端节点（0-terminal）。
constexpr int DD_ZERO_TERM =
    -2;  // represents the $\bot$-terminal node of DanceDD
constexpr int MAX_DEPTH = 1000;  // maximum depth of the search tree.
using nstack_t = std::stack<int32_t>;// 定义节点栈类型
using count_t = uint32_t;// 计数类型

/**
 * type of parent links
 * lower 2 bits are used for flags, remaining bits are used for showing parent
 * nodes.
 * 父链接类型
 * 低2位用于标志，其余位用于存储父节点信息
 */
using plink_t = uint32_t;
constexpr uint32_t PLINK_IS_TERMINAL = 2LU; // 终端节点标志
constexpr uint32_t PLINK_IS_HI = 1LU;       // HI（1-分支）链接标志
constexpr uint32_t PLINK_ADDR_OFFSET = 2LU; // 地址偏移量
// PLINK_ADDR_OFFSET 定义了父链接地址的位移量，用于确保在节点引用中的正确定位

/**
 * Node cell
 * @attr var: corresponding variable
 * @attr hi: node cell id of hi-child
 * @attr lo: node cell id of lo-child
 * @attr up: id of the previous node cell having the same var. If no such cell
 exist, the value is -1.
 * @attr down: id of the next node cell having the same var. If no such cell
 exist, the value is -1.
 * @attr parents_head: head of the parent node list.
 * @attr parents_tail: tail of the parent ndoe list.
 * @attr hi_next: the next edge of hi-edge pointing to the same child node.
 * @attr hi_prev: the previous edge of hi-edge pointing to the same child node.
 * @attr lo_next: the next edge of lo-edge pointing to the same child node.
 * @attr lo_prev: the previous edge of lo-edge pointing to the same child node.
 * @attr count_upper: number of routes from the root danceDD node.
 * @attr count_hi: the number of routes from the hi-child to TOP-terminal.
 * @attr count_lo: the number of routes from the lo-child to TOP-terminal.
 * 节点单元
 * @attr var：对应的变量
 * @attr hi: hi子节点的节点单元id
 * @attr lo: lo-child的节点单元id
 * @attr up：具有相同var的前一个节点单元的id，如果没有这样的单元存在，取值为-1。
 * @attr down：具有相同var的下一个节点单元的id，如果没有这样的单元存在，取值为-1。
 * @attr parents_head：父节点列表的头部。
 * @attr parents_tail：父ndoe列表的尾部。
 * @attr hi_next：指向同一子节点的hi-edge的下一条边。
 * @attr hi_prev：指向同一子节点的高边的前一条边
 * @attr lo_next：指向同一子节点的lo-edge的下一个边。
 * @attr lo_prev：指向同一子节点的lo_edge的前一条边
 * @attr count_upper：来自根节点danceDD的路由数。
 * @attr count_hi：从hi-child到TOP-terminal的路由数。
 * @attr count_lo：从lo子节点到TOP-terminal的路由数。
 */
struct Node {
   public:
   /**
     * @brief 构造函数，初始化节点。
     * @param var 变量编号。
     * @param hi 1-分支的子节点 ID。
     * @param lo 0-分支的子节点 ID。
     */
    Node(uint16_t var, int32_t hi, int32_t lo)
        : hi(hi),
          lo(lo),
          up(-1),
          down(-1),
          parents_head(0),
          parents_tail(0),
          hi_next(0),
          hi_prev(0),
          lo_next(0),
          lo_prev(0),
          count_hi(0),
          count_lo(0),
          count_upper(0),
          var(var),
          padding(0) {}
    // 拷贝构造
    Node(const Node &obj)
        : hi(obj.hi),
          lo(obj.lo),
          up(obj.up),
          down(obj.down),
          parents_head(obj.parents_head),
          parents_tail(obj.parents_tail),
          hi_next(obj.hi_next),
          hi_prev(obj.hi_prev),
          lo_next(obj.lo_next),
          lo_prev(obj.lo_prev),
          count_hi(obj.count_hi),
          count_lo(obj.count_lo),
          count_upper(obj.count_upper),
          var(obj.var),
          padding(obj.padding) {}
    // 操作符重载
    bool operator==(const Node &obj) const {
        return var == obj.var && hi == obj.hi && lo == obj.lo && up == obj.up &&
               down == obj.down && parents_head == obj.parents_head &&
               parents_tail == obj.parents_tail && hi_next == obj.hi_next &&
               hi_prev == obj.hi_prev && lo_next == obj.lo_next &&
               lo_prev == obj.lo_prev && count_upper == obj.count_upper &&
               count_hi == obj.count_hi && count_lo == obj.count_lo;
    }
    // 判断两个node是否不相同
    bool operator!=(const Node &obj) const { return !(*this == obj); }
    int32_t hi;
    int32_t lo;
    int32_t up;
    int32_t down;
    plink_t parents_head;
    plink_t parents_tail;
    plink_t hi_next;
    plink_t hi_prev;
    plink_t lo_next;
    plink_t lo_prev;
    count_t count_hi;
    count_t count_lo;
    count_t count_upper;
    uint16_t var;// Variable associated with this node.
    uint16_t padding;// Padding for memory alignment.
};

/**
 * Header cell of DanceDD
 * @attr left: id of the prevous header cell
 * @attr right: id of the next header cell.
 * @attr down: id of the first node cell id having the same var. -1 if empty
 * @attr up: id of the last node cell id having the same var. -1 if empty
 * @attr var: corresponding variable
 * @attr count: number of options having the variable
 * DanceDD的Header结构，管理变量列。
 * @attr左：前一个标题单元格的id
 * @attr right：下一个标题单元格的id。
 * @attr down：具有相同var的第一个节点单元id的id，如果为空则为-1
 * @attr up：具有相同var的最后一个节点单元id的id，如果为空则为-1
 * @attr var：对应的变量
 * @attr count：拥有该变量的选项数
 */
struct Header {
   public:
    Header(int16_t left, int16_t right, int32_t down, int32_t up, uint16_t var,
           count_t count)
        : left(left),
          right(right),
          var(var),
          padding1(0),
          down(down),
          up(up),
          count(count),
          padding2(0) {}

    bool operator==(const Header &o) const {
        return (left == o.left && right == o.right && down == o.down &&
                up == o.up && var == o.var && count == o.count);
    }

    bool operator!=(const Header &o) const { return !((*this) == o); }

    int16_t left;
    int16_t right;
    uint16_t var;
    uint16_t padding1;  // dummy value Padding for memory alingnment
    int32_t down;
    int32_t up;
    count_t count;
    int32_t padding2;   // additional padding
};

/**
 * DanceDD structure
 * 主类表示具有附加链接功能的ZDD。
 */
class ZddWithLinks {
   public:
    // 用于各种操作的静态计数器。
    static uint64_t num_search_tree_nodes; // 搜索树节点的数量
    static uint64_t num_solutions;         // 解决方案的数量
    static uint64_t num_updates;           // 更新操作的数量
    static uint64_t num_head_updates;      // 头部更新的数量
    static uint64_t num_inactive_updates;  // 非活动更新的数量
    static uint64_t num_hides;             // 隐藏操作的数量
    static uint64_t num_failure_backtracks;// 失败回溯的数量

    ZddWithLinks(int num_var, bool sanity_check = false);
    ZddWithLinks(const ZddWithLinks &obj);

    bool operator==(const ZddWithLinks &obj) const;

    /**
     *递归搜索解决方案。
     *@param solution-存储已找到解决方案。
     *@param depth-当前搜索深度。
     */
    void search(vector<vector<uint16_t>> &solution, const int depth);

    /**
     * @brief 从文件加载ZDD数据。
     * @param file_name ZDD文件名。
     */
    void load_zdd_from_file(const string &file_name);

    /**
     * @brief 检查DanceDD结构的有效性。
     * @return 如果存在错误则返回 true，否则返回 false。
     */
    bool sanity() const;

   private:
    /***
     * parent link operation methods.
     *
     */

    /**
     * @brief 检查给定的父链接地址是否指向高分支（hi）。
     * @param addr 父链接地址。
     * @return 如果是高分支返回 true，否则返回 false。
     */
    inline bool plink_is_hi(plink_t addr) const { return addr & PLINK_IS_HI; }

    /**
     * @brief 检查给定的父链接地址是否指向终端节点。
     * @param addr 父链接地址。
     * @return 如果是终端节点返回 true，否则返回 false。
     */
    inline bool plink_is_term(plink_t addr) const {
        return addr & PLINK_IS_TERMINAL;
    }

    /**
     * @brief 获取给定父链接地址指向的节点ID。
     * @param addr 父链接地址。
     * @return 指向的节点ID。
     */
    inline plink_t plink_node_id(plink_t addr) const {
        return addr >> PLINK_ADDR_OFFSET;
    }

    /**
     * @brief 设置父链接地址的前一个链接。
     * @param addr 父链接地址。
     * @param val 要设置的值。
     */
    inline void plink_set_prev(plink_t addr, plink_t val) {
        assert((addr & 3LU) != 3LU);
        assert((val & 3LU) != 3LU);
        Node &node = table_[plink_node_id(addr)];
        if (plink_is_hi(addr)) {
            node.hi_prev = val;
        } else if (plink_is_term(addr)) {
            node.parents_tail = val;
        } else {
            node.lo_prev = val;
        }
    }

    /**
     * @brief 设置父链接地址的下一个链接。
     * @param addr 父链接地址。
     * @param val 要设置的值。
     */
    inline void plink_set_next(plink_t addr, plink_t val) {
        assert((addr & 3LU) != 3LU);
        assert((val & 3LU) != 3LU);
        Node &node = table_[plink_node_id(addr)];
        if (plink_is_hi(addr)) {
            node.hi_next = val;
        } else if (plink_is_term(addr)) {
            node.parents_head = val;
        } else {
            node.lo_next = val;
        }
    }

    /**
     * @brief 获取父链接地址的前一个链接。
     * @param addr 父链接地址。
     * @return 前一个链接地址。
     */
    inline plink_t plink_get_prev(plink_t addr) const {
        assert((addr & 3LU) != 3LU);

        const Node &node = table_[plink_node_id(addr)];

        if (plink_is_hi(addr)) {
            return node.hi_prev;
        } else if (plink_is_term(addr)) {
            return node.parents_tail;
        } else {
            return node.lo_prev;
        }
    }

    /**
     * @brief 获取父链接地址的下一个链接。
     * @param addr 父链接地址。
     * @return 下一个链接地址。
     */
    inline plink_t plink_get_next(plink_t addr) const {
        assert((addr & 3LU) != 3LU);
        const Node &node = table_[plink_node_id(addr)];

        if (plink_is_hi(addr)) {
            return node.hi_next;
        } else if (plink_is_term(addr)) {
            return node.parents_head;
        } else {
            return node.lo_next;
        }
    }

    /**
     * @brief 初始化舞动链接结构。
     * @details 设置节点计数、初始化上下链接关系以及管理动态规划。
     */
    void setup_dancing_links();

    /**
     * @brief 批量覆盖给定列。
     * @param col_begin 列开始的迭代器。
     * @param col_end 列结束的迭代器。
     * @details 通过覆盖列来更新数据结构，隐藏相关节点。
     */
    void batch_cover(const std::vector<uint16_t>::const_iterator col_begin,
                     const std::vector<uint16_t>::const_iterator col_end);

    /**
     * @brief 批量取消覆盖给定列。
     * @param col_begin 列开始的迭代器。
     * @param col_end 列结束的迭代器。
     * @details 通过取消覆盖列来恢复数据结构，显示相关节点。
     */
    void batch_uncover(const std::vector<uint16_t>::const_iterator col_begin,
                       const std::vector<uint16_t>::const_iterator col_end);

    /**
     * @brief 计算上方向的选择。
     * @param node_id 当前节点ID。
     * @param up_id 上方向计数ID。
     * @param choice 输出选择的列。
     * @details 根据当前节点和计数ID，计算出上方向的选择路径。
     */
    void compute_upper_choice(int32_t node_id, count_t up_id,
                              vector<uint16_t> &choice) noexcept;

    /**
     * @brief 初始化上方向的选择。
     * @param node_id 起始节点ID。
     * @param visited 已访问的节点列表。
     * @param diff_choices 变化的选择索引。
     * @param diff_choice_ids 变化的选择节点ID。
     * @param choices_buf 用于存储选择的缓冲区。
     * @details 初始化上方向的选择路径，记录访问的节点和变化的选择。
     */
    void compute_upper_initial_choice(int32_t node_id,
                                      vector<uint32_t> &visited,
                                      vector<size_t> &diff_choices,
                                      vector<int32_t> &diff_choice_ids,
                                      vector<uint16_t> &choices_buf) noexcept;

    /**
     * @brief 计算上方向的下一个选择。
     * @param visited 已访问的节点列表。
     * @param diff_choices 变化的选择索引。
     * @param diff_choice_ids 变化的选择节点ID。
     * @param choice_buf 用于存储选择的缓冲区。
     * @return 如果没有更多选择则返回 true，否则返回 false。
     * @details 计算上方向的下一个选择路径，更新访问的节点和变化的选择。
     */
    bool compute_upper_next_choice(vector<uint32_t> &visited,
                                   vector<size_t> &diff_choices,
                                   vector<int32_t> &diff_choice_ids,
                                   vector<uint16_t> &choice_buf);

    /**
     * @brief 计算下方向的选择。
     * @param node_id 当前节点ID。
     * @param down_id 下方向计数ID。
     * @param choice 输出选择的列。
     * @details 根据当前节点和计数ID，计算出下方向的选择路径。
     */
    void compute_lower_choice(int32_t node_id, count_t down_id,
                              vector<uint16_t> &choice) noexcept;

    /**
     * @brief 初始化下方向的选择。
     * @param start_id 起始节点ID。
     * @param visited 已访问的节点列表。
     * @param diff_choices 变化的选择索引。
     * @param choices_buf 用于存储选择的缓冲区。
     * @details 初始化下方向的选择路径，记录访问的节点和变化的选择。
     */
    void compute_lower_initial_choice(const int32_t start_id,
                                      vector<uint32_t> &visited,
                                      vector<size_t> &diff_choices,
                                      vector<uint16_t> &choices_buf);

    /**
     * @brief 计算下方向的下一个选择。
     * @param visited 已访问的节点列表。
     * @param diff_choices 变化的选择索引。
     * @param choice_buf 用于存储选择的缓冲区。
     * @return 如果没有更多选择则返回 true，否则返回 false。
     * @details 计算下方向的下一个选择路径，更新访问的节点和变化的选择。
     */
    bool compute_lower_next_choice(vector<uint32_t> &visited,
                                   vector<size_t> &diff_choices,
                                   vector<uint16_t> &choice_buf);

    /**
     * @brief 将跟踪信息转换为选择集。
     * @tparam ForwardIterator 输入迭代器类型。
     * @param begin 选择的开始迭代器。
     * @param end 选择的结束迭代器。
     * @param choice 输出的选择集缓冲区。
     */
    template <typename ForwardIterator>
    void trace2choice(ForwardIterator begin, ForwardIterator end,
                      vector<uint16_t> &choice) const {
        choice.clear();
        for (auto it = begin; it != end; ++it) {
            uint32_t val = *it;
            if (val & 1U) {
                choice.push_back(table_[val >> 1U].var);
            }
        }
    }

    /**
     * @brief 隐藏指定的节点。
     * @param node_id 要隐藏的节点ID。
     */
    void hide_node(const int32_t node_id);

    /**
     * @brief 隐藏cover_down类型的节点。
     * @param node_id 要隐藏的节点ID。
     */
    void hide_node_cover_down(const int32_t node_id);

    /**
     * @brief 隐藏cover_up类型的节点。
     * @param node_id 要隐藏的节点ID。
     */
    void hide_node_cover_up(const int32_t node_id);

    /**
     * @brief 隐藏upperzero类型的节点。
     * @param node_id 要隐藏的节点ID。
     */
    void hide_node_upperzero(const int32_t node_id);

    /**
     * @brief 隐藏lowerzero类型的节点。
     * @param node_id 要隐藏的节点ID。
     */
    void hide_node_lowerzero(const int32_t node_id);

    /**
     * @brief 取消隐藏指定的节点。
     * @param node_id 要取消隐藏的节点ID。
     */
    void unhide_node(const int32_t node_id);
    
    /**
     * @brief 取消隐藏cover_down类型的节点。
     * @param node_id 要取消隐藏的节点ID。
     */
    void unhide_node_cover_down(const int32_t node_id);

    /**
     * @brief 取消隐藏cover_up类型的节点。
     * @param node_id 要取消隐藏的节点ID。
     */
    void unhide_node_cover_up(const int32_t node_id);

    /**
     * @brief 取消隐藏upperzero类型的节点。
     * @param node_id 要取消隐藏的节点ID。
     */
    void unhide_node_upperzero(const int32_t node_id);

    /**
     * @brief 取消隐藏lowerzero类型的节点。
     * @param node_id 要取消隐藏的节点ID。
     */
    void unhide_node_lowerzero(const int32_t node_id);

    /**
     * @brief 打印指定节点的父链接信息，用于调试。
     * @param node_id 要打印的节点ID。
     */
    void print_parent_links(const int32_t node_id) const {
        const Node &node = table_[node_id];
        std::cerr << node_id << ", ";
        for (plink_t plink = node.parents_head;;
             plink = plink_get_next(plink)) {
            auto pid = plink_node_id(plink);
            auto is_hi = plink_is_hi(plink);
            auto is_term = plink_is_term(plink);

            std::cerr << "(" << pid << ", " << table_[pid].var << ", ";
            if (is_hi) {
                std::cerr << "HI), ";
            } else if (is_term) {
                std::cerr << "TERM), abort!";
                break;
            } else {
                std::cerr << "LO), ";
            }
            if (plink == node.parents_tail) {
                break;
            }
        }
        std::cerr << endl;
    }

    // ZDD中变量的数量
    const int num_var_;

    // 存储节点单元的向量
    vector<Node> table_;

    // 存储头部单元的向量
    vector<Header> header_;

    // 动态规划管理器的智能指针
    unique_ptr<DpManager> dp_mgr_;

    // 隐藏节点栈的智能指针
    unique_ptr<HiddenNodeStack> hidden_node_stack_;

    // 是否进行完整性检查的标志
    const bool sanity_check_;

    // 搜索过程中每个深度的选择缓冲区
    vector<vector<uint16_t>> depth_choice_buf_;

    // 上方向选择的缓冲区。用于记录和管理上方向的选择路径。
    vector<vector<uint16_t>> depth_upper_choice_buf_;

    // 下方向选择的缓冲区
    vector<vector<uint16_t>> depth_lower_choice_buf_;

    // 下方向的跟踪信息缓冲区
    vector<vector<uint32_t>> depth_lower_trace_buf_;

    // 下方向选择变化的索引缓冲区
    vector<vector<size_t>> depth_lower_change_pts_buf_;

    // 上方向的跟踪信息缓冲区。帮助在搜索过程中记录访问的节点和路径。
    vector<vector<uint32_t>> depth_upper_trace_buf_;

    // 上方向选择变化的索引缓冲区。用于记录和管理选择路径中涉及的节点变化。
    vector<vector<size_t>> depth_upper_change_pts_buf_;

    // 上方向选择变化的节点ID缓冲区。用于记录和管理选择路径中涉及的节点变化。
    vector<vector<int32_t>> depth_upper_change_node_ids_buf_;
};
#endif  // DANCING_ON_ZDD_H_