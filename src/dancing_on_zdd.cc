// dancing_on_zdd.h 头文件的实现文件
// 该文件实现了 ZddWithLinks 类的功能，主要用于管理和操作具有附加链接功能的 ZDD 结构。

#include "dancing_on_zdd.h"

#include <unordered_map>
#include <unordered_set>

#include "dp_manager.h"
// 引入 DpManager 类用于管理动态规划相关的操作，提升搜索与覆盖效率

// 初始化静态计数器变量，用于跟踪ZDD操作的统计信息
uint64_t ZddWithLinks::num_inactive_updates = 0UL;
uint64_t ZddWithLinks::num_search_tree_nodes = 0UL;
uint64_t ZddWithLinks::num_updates = 0UL;
uint64_t ZddWithLinks::num_head_updates = 0UL;
uint64_t ZddWithLinks::num_solutions = 0UL;
uint64_t ZddWithLinks::num_hides = 0UL;
uint64_t ZddWithLinks::num_failure_backtracks = 0UL;

/**
 * ZddWithLinks 类的构造函数
 * @param num_var 变量的数量。
 * @param sanity_check 是否进行一致性检查。
 * 初始化 ZDD 结构，设置节点和头部单元，并准备动态规划管理器和隐藏节点栈。
 */
ZddWithLinks::ZddWithLinks(int num_var, bool sanity_check)
    : num_var_(num_var),
      table_(),
      dp_mgr_(nullptr),
      hidden_node_stack_(make_unique<HiddenNodeStack>(HiddenNodeStack())),
      sanity_check_(sanity_check),
      depth_choice_buf_(MAX_DEPTH, std::vector<uint16_t>()),
      depth_upper_choice_buf_(MAX_DEPTH, std::vector<uint16_t>()),
      depth_lower_choice_buf_(MAX_DEPTH, std::vector<uint16_t>()),
      depth_lower_trace_buf_(MAX_DEPTH, std::vector<uint32_t>()),
      depth_lower_change_pts_buf_(MAX_DEPTH, std::vector<size_t>()),
      depth_upper_trace_buf_(MAX_DEPTH, std::vector<uint32_t>()),
      depth_upper_change_pts_buf_(MAX_DEPTH, std::vector<size_t>()),
      depth_upper_change_node_ids_buf_(MAX_DEPTH, std::vector<int32_t>()) {
    // 初始化头部单元，管理变量列。
    header_.emplace_back(num_var_, 1, -1, -1, 0, 0);  // 头部单元的头部
    for (int i = 0; i < num_var_; i++) {
        header_.emplace_back(i, i + 2, -1, -1, i + 1, 0);  // 初始化每个变量的头部单元
    }
    header_[num_var].right = 0;  // 设置最后一个头部单元的右链接为0，表示结束
}

/**
 * ZddWithLinks 类的拷贝构造函数
 * @param obj 要复制的 ZddWithLinks 对象。
 * 复制 ZDD 结构的节点和头部单元，但不复制动态规划管理器和隐藏节点栈。
 */
ZddWithLinks::ZddWithLinks(const ZddWithLinks &obj)
    : num_var_(obj.num_var_),
      table_(obj.table_),
      header_(obj.header_),
      dp_mgr_(nullptr),
      hidden_node_stack_(nullptr),
      sanity_check_(false),
      depth_choice_buf_(MAX_DEPTH, std::vector<uint16_t>()),
      depth_upper_choice_buf_(MAX_DEPTH, std::vector<uint16_t>()),
      depth_lower_choice_buf_(MAX_DEPTH, std::vector<uint16_t>()) {}

/**
 * 操作符重载，用于调试时比较两个 ZddWithLinks 对象是否相等
 * @param obj 要比较的 ZddWithLinks 对象。
 * @return 如果两个对象相等则返回 true，否则返回 false。
 */
bool ZddWithLinks::operator==(const ZddWithLinks &obj) const {
    if (num_var_ != obj.num_var_) return false;

    if (table_.size() != obj.table_.size()) return false;
    bool equals = true;
    for (size_t i = 0; i < table_.size(); i++) {
        if (table_[i] != obj.table_[i]) {
            fprintf(stderr, "node %lu differs\n", i);
            equals = false;
        }
    }

    for (size_t i = 0; i < header_.size(); i++) {
        if (header_[i] != obj.header_[i]) {
            fprintf(stderr, "header %lu differs\n", i);
            equals = false;
        }
    }
    return equals;
}

/**
 * 递归搜索 ZDD 结构中的解决方案。
 * @param solution 存储已找到的解决方案。
 * @param depth 当前搜索深度。
 * 通过递归搜索，找到所有可能的解决方案。
 */
void ZddWithLinks::search(vector<vector<uint16_t>> &solution, const int depth) {
    num_search_tree_nodes++;

    if (header_[0].right == 0)  // 所有列都被覆盖
    {
        num_solutions += 1;
        return;
    }

    // 选择具有最小选项数的列
    count_t min_count = UINT32_MAX;
    int min_count_column = -1;
    int remain_cols = 0;
    for (int head_pos = header_[0].right; head_pos != 0;
         head_pos = header_[head_pos].right) {
        const Header &header = header_[head_pos];
        remain_cols++;

        if (header.count == 0) {
            // 无法覆盖列，回溯。
            num_failure_backtracks++;
            return;
        }

        if (header.count < min_count) {
            min_count_column = head_pos;
            min_count = header.count;
        }
    }

    depth_choice_buf_[depth].clear();
    depth_choice_buf_[depth].push_back((uint16_t)min_count_column);
    batch_cover(std::cbegin(depth_choice_buf_[depth]),
                std::cend(depth_choice_buf_[depth]));
    int node_id = header_[min_count_column].down;

    int lower_change_idx = -1;

    while (node_id >= 0) {
        // 选择一个选项并覆盖列
        const Node &node = table_[node_id];

        for (auto up_id = 0; up_id < node.count_upper; ++up_id) {
            compute_upper_choice(node_id, up_id,
                                 depth_upper_choice_buf_[depth]);
            reverse(depth_upper_choice_buf_[depth].begin(),
                    depth_upper_choice_buf_[depth].end());
            batch_cover(depth_upper_choice_buf_[depth].begin(),
                        depth_upper_choice_buf_[depth].end());

            compute_lower_initial_choice(node.hi, depth_lower_trace_buf_[depth],
                                         depth_lower_change_pts_buf_[depth],
                                         depth_lower_choice_buf_[depth]);
            for (;;) {
                search(solution, depth + 1);

                bool finished = compute_lower_next_choice(
                    depth_lower_trace_buf_[depth],
                    depth_lower_change_pts_buf_[depth],
                    depth_lower_choice_buf_[depth]);
                if (finished) break;
            }
            batch_uncover(depth_upper_choice_buf_[depth].begin(),
                          depth_upper_choice_buf_[depth].end());
        }

        node_id = node.down;
    }

    batch_uncover(std::cbegin(depth_choice_buf_[depth]),
                  std::cend(depth_choice_buf_[depth]));

    if (sanity_check_ && sanity()) {
        cerr << "inconsistent after uncover" << endl;
    }

    return;
}

/**
 * 从文件加载ZDD数据。
 * @param file_name ZDD文件名。
 * 读取文件内容并将其解析为ZDD结构。
 */
void ZddWithLinks::load_zdd_from_file(const string &file_name) {
    ifstream ifs(file_name);

    if (!ifs) {
        cerr << "can't open " << file_name << endl;
        exit(1);
    }

    string line;

    unordered_map<int, int> id_convert_table;

    while (getline(ifs, line)) {
        if (line[0] == '.' || line[0] == '\n' || line[0] == '#' || line.size() == 0) continue;

        istringstream iss(line);
        int nid;
        int var;
        string lo_str;
        int lo_id;
        string hi_str;
        int hi_id;
        iss >> nid;
        iss >> var;
        iss >> lo_str;
        iss >> hi_str;

        id_convert_table[nid] = table_.size();
        if (lo_str[0] == 'B') {
            lo_id = DD_ZERO_TERM;
        } else if (lo_str[0] == 'T') {
            lo_id = DD_ONE_TERM;
        } else {
            lo_id = id_convert_table[stoi(lo_str)];
        }
        if (hi_str[0] == 'B') {
            hi_id = DD_ZERO_TERM;
        } else if (hi_str[0] == 'T') {
            hi_id = DD_ONE_TERM;
        } else {
            hi_id = id_convert_table[stoi(hi_str)];
        }
        table_.emplace_back(var, hi_id, lo_id);
    }

    setup_dancing_links();
}

/**
 * 批量覆盖给定的列。
 * @param col_begin 列开始的迭代器。
 * @param col_end 列结束的迭代器。
 * 通过覆盖列来更新数据结构，隐藏相关节点。
 */
void ZddWithLinks::batch_cover(
    const std::vector<uint16_t>::const_iterator col_begin,
    const std::vector<uint16_t>::const_iterator col_end) {
    assert(is_sorted(col_begin, col_end));
    if (col_begin == col_end) {
        return;
    }
    // 覆盖头部
    for (auto it = col_begin; it != col_end; ++it) {
        const auto col = *it;
        num_head_updates++;
        auto cleft = header_[col].left, cright = header_[col].right;
        header_[cleft].right = cright;
        header_[cright].left = cleft;
    }

    hidden_node_stack_->push_checkpoint();
    {
        auto next_cover_column = col_begin;
        auto var = *next_cover_column;
        for (auto it = col_begin; it != col_end; ++it) {
            const auto col = *it;
            dp_mgr_->add_lower_var(col);
        }
        for (auto var = dp_mgr_->lower_nonzero_var(); var != 0;
             var = dp_mgr_->lower_nonzero_var()) {
            auto &var_head = header_[var];
            if (next_cover_column != col_end && var == *next_cover_column) {
                next_cover_column++;

                for (auto node_id = header_[var].down; node_id >= 0;
                     node_id = table_[node_id].down) {
                    num_updates++;
                    Node &node = table_[node_id];

                    assert(node.count_upper > 0);
                    assert(node.count_hi > 0);
                    auto nhi = node.hi, nlo = node.lo;
                    if (nhi >= 0 && node.count_hi > 0 && node.count_upper > 0) {
                        dp_mgr_->add_node_diff_count(table_[nhi].var, nhi,
                                                     node.count_upper);
                    }

                    const auto count_diff_upper =
                        dp_mgr_->get_count_and_clear(node_id);
                    if (count_diff_upper > 0 && nlo >= 0) {
                        dp_mgr_->add_node_diff_count(table_[nlo].var, nlo,
                                                     count_diff_upper);
                    }
                    node.count_upper -= count_diff_upper;
                    var_head.count -= count_diff_upper * node.count_hi;

                    if (node.count_upper == 0) {
                        num_hides++;
                        auto nup = node.up, ndown = node.down;
                        if (nup >= 0) {
                            table_[nup].down = ndown;
                        } else {
                            var_head.down = ndown;
                        }
                        if (ndown >= 0) {
                            table_[ndown].up = nup;
                        } else {
                            var_head.up = nup;
                        }

                        hide_node_upperzero(node_id);
                        hidden_node_stack_->push_upperzero(node_id);
                    }
                }
            } else {  // var が cover_columnsではなかった場合

                for (size_t i = 0; i < dp_mgr_->num_elems(var); i++) {
                    num_updates++;

                    const auto node_id = dp_mgr_->at(var, i);
                    Node &node = table_[node_id];

                    assert(node.count_upper > 0);

                    const auto upper_count =
                        dp_mgr_->get_count_and_clear(node_id);
                    node.count_upper -= upper_count;
                    var_head.count -= upper_count * node.count_hi;

                    assert(upper_count > 0);
                    assert(node.count_hi > 0);
                    auto nhi = node.hi, nlo = node.lo;
                    if (nhi >= 0 && node.count_hi > 0 && upper_count > 0) {
                        dp_mgr_->add_node_diff_count(table_[nhi].var, nhi,
                                                     upper_count);
                    }
                    if (nlo >= 0 && upper_count > 0 && node.count_lo > 0) {
                        dp_mgr_->add_node_diff_count(table_[nlo].var, nlo,
                                                     upper_count);
                    }

                    // 隐藏节点
                    if (node.count_upper == 0) {
                        num_hides++;
                        auto nup = node.up, ndown = node.down;
                        if (nup >= 0) {
                            table_[nup].down = ndown;
                        } else {
                            var_head.down = ndown;
                        }
                        if (ndown >= 0) {
                            table_[ndown].up = nup;
                        } else {
                            var_head.up = nup;
                        }

                        hide_node_upperzero(node_id);
                        hidden_node_stack_->push_upperzero(node_id);
                    }
                }
            }
            // 清除动态规划计数器
            dp_mgr_->clear_var_counter(var);
        }
    }

    hidden_node_stack_->reverse_current_stack();
    for (auto it = hidden_node_stack_->stack_cbegin();
         it != hidden_node_stack_->stack_cend(); ++it) {
        auto [node_id, hide_type] = *it;

        Node &node = table_[node_id];
        auto nup = node.up, ndown = node.down;

        switch (hide_type) {
            case HiddenNodeStack::HideType::CoverUp:
                hide_node_cover_up(node_id);
                break;
            case HiddenNodeStack::HideType::LowerZero:

                if (nup >= 0) {
                    table_[nup].down = ndown;
                } else {
                    header_[node.var].down = ndown;
                }
                if (ndown >= 0) {
                    table_[ndown].up = nup;
                } else {
                    header_[node.var].up = nup;
                }
                hide_node_lowerzero(node_id);
                break;
            default:
                assert(false);
                cerr << "error: hide_node type must be either of CoverUp or "
                        "LowerZero"
                     << endl;
                exit(1);
        }
    }
}

/**
 * 批量取消覆盖给定的列。
 * @param col_begin 列开始的迭代器。
 * @param col_end 列结束的迭代器。
 * 通过取消覆盖列来恢复数据结构，显示相关节点。
 */
void ZddWithLinks::batch_uncover(
    const std::vector<uint16_t>::const_iterator col_begin,
    const std::vector<uint16_t>::const_iterator col_end) {
    assert(is_sorted(col_begin, col_end));
    if (col_begin == col_end) {
        return;
    }
    // cerr << "batch uncover:";
    // for (auto it = col_begin; it != col_end; ++it) {
    //     cerr << *it << ",";
    // }
    //    cerr << endl;
    // 取消覆盖列头
    const auto col_rbegin = std::make_reverse_iterator(col_end);
    const auto col_rend = std::make_reverse_iterator(col_begin);
    for (auto it = col_rbegin; it != col_rend; ++it) {
        auto col = *it;
        auto left = header_[col].left, right = header_[col].right;
        assert(header_[left].right == right && header_[right].left == left);
        header_[left].right = col;
        header_[right].left = left;
    }

    // batch_coverの上方向dpでhideしたノードをすべてunhideする．
    while (!hidden_node_stack_->is_empty()) {
        auto [node_id, hide_type] = hidden_node_stack_->top();
        hidden_node_stack_->pop();

        switch (hide_type) {
            case HiddenNodeStack::HideType::CoverUp:
                unhide_node_cover_up(node_id);
                break;

            case HiddenNodeStack::HideType::LowerZero:
                unhide_node_lowerzero(node_id);

                {
                    auto nup = table_[node_id].up, ndown = table_[node_id].down;
                    auto nvar = table_[node_id].var;

                    if (nup >= 0) {
                        table_[nup].down = node_id;
                    } else {
                        header_[nvar].down = node_id;
                    }
                    if (ndown >= 0) {
                        table_[ndown].up = node_id;
                    } else {
                        header_[nvar].up = node_id;
                    }
                }
                break;

            default:
                assert(false);
                cerr << "error: hide_node type must be either of CoverUp "
                        "or LowerZero"
                     << endl;
                exit(1);
        }
    }
    hidden_node_stack_->pop_checkpoint();

    {
        for (auto it = col_begin; it != col_end; ++it) {
            dp_mgr_->add_lower_var(*it);
        }
        auto next_cover_column = col_begin;
        for (auto var = dp_mgr_->lower_nonzero_var(); var != 0;
             var = dp_mgr_->lower_nonzero_var()) {
            if (next_cover_column != col_end && var == *next_cover_column) {
                next_cover_column++;

                for (auto node_id = header_[var].down; node_id >= 0;
                     node_id = table_[node_id].down) {
                    Node &node = table_[node_id];

                    assert(node.count_hi > 0);

                    const auto count_diff_upper =
                        dp_mgr_->get_count_and_clear(node_id);
                    node.count_upper += count_diff_upper;
                    header_[var].count += count_diff_upper * node.count_hi;
                    auto nhi = node.hi, nlo = node.lo;
                    //                    if (nhi >= 0) {
                    if (nhi >= 0 && node.count_hi > 0 && node.count_upper > 0) {
                        dp_mgr_->add_node_diff_count(table_[nhi].var, nhi,
                                                     node.count_upper);
                    }

                    if (count_diff_upper > 0 && nlo >= 0) {
                        dp_mgr_->add_node_diff_count(table_[nlo].var, nlo,
                                                     count_diff_upper);
                    }
                }
            } else {  // var が cover_columnsではなかった場合
                auto &var_head = header_[var];
                for (size_t i = 0; i < dp_mgr_->num_elems(var); i++) {
                    const auto node_id = dp_mgr_->at(var, i);
                    Node &node = table_[node_id];

                    const auto upper_count =
                        dp_mgr_->get_count_and_clear(node_id);
                    node.count_upper += upper_count;
                    assert(node.count_upper > 0);

                    var_head.count += upper_count * node.count_hi;

                    assert(upper_count > 0);
                    assert(node.count_hi > 0);
                    auto nhi = node.hi, nlo = node.lo;
                    if (nhi >= 0 && node.count_hi > 0 && upper_count > 0) {
                        dp_mgr_->add_node_diff_count(table_[nhi].var, nhi,
                                                     upper_count);
                    }

                    if (nlo >= 0 && node.count_lo > 0) {
                        dp_mgr_->add_node_diff_count(table_[nlo].var, nlo,
                                                     upper_count);
                    }
                }
            }

            dp_mgr_->clear_var_counter(var);
        }
    }
}

/**
 * 设置舞动链接结构，初始化节点计数和链接关系。
 * 初始化节点的计数和链接关系，准备动态规划管理器。
 */
void ZddWithLinks::setup_dancing_links() {
    // 初始化节点的计数
    for (Node &node : table_) {
        node.count_upper = 0;
        node.count_lo = 0;
        node.count_hi = 0;
    }
    // 计算下方向的计数
    for (size_t i = 0; i < table_.size(); i++) {
        Node &node = table_[i];
        if (node.lo == DD_ZERO_TERM) {
            node.count_lo = 0;
        } else if (node.lo == DD_ONE_TERM) {
            node.count_lo = 1;
        } else if (node.lo >= 0) {
            node.count_lo = table_[node.lo].count_lo + table_[node.lo].count_hi;
        }
        if (node.hi == DD_ZERO_TERM) {
            node.count_hi = 0;
        } else if (node.hi == DD_ONE_TERM) {
            node.count_hi = 1;
        } else if (node.hi >= 0) {
            node.count_hi = table_[node.hi].count_lo + table_[node.hi].count_hi;
        }
    }

    // 计算上方向的计数
    table_[table_.size() - 1].count_upper = 1;
    for (int i = table_.size() - 1; i >= 0; i--) {
        Node &node = table_[i];
        if (node.hi >= 0) {
            table_[node.hi].count_upper += node.count_upper;
        }
        if (node.lo >= 0) {
            table_[node.lo].count_upper += node.count_upper;
        }
    }
    // 设置上下链接
    for (size_t i = 0; i < table_.size(); i++) {
        Node &node = table_[i];
        Header &header = header_[node.var];
        if (header.up >= 0) {
            Node &prev = table_[header.up];
            prev.down = i;
            node.up = header.up;
            node.down = -1;
            header.up = i;
        } else {
            header.down = i;
            header.up = i;
            node.up = -1;
            node.down = -1;
        }
        count_t counts = 0;
        if (node.hi == DD_ONE_TERM) {
            counts = node.count_upper;
        } else if (node.hi >= 0) {
            counts = node.count_upper * node.count_hi;
        }
        header.count += counts;
    }
    // 设置父节点单元
    for (size_t i = 0; i < table_.size(); i++) {
        Node &node = table_[i];

        node.parents_head = i << 2UL | 2UL;
        node.parents_tail = i << 2UL | 2UL;

        if (node.hi >= 0) {
            Node &child = table_[node.hi];
            node.hi_prev = child.parents_tail;
            node.hi_next = node.hi << 2UL | 2UL;
            plink_set_next(child.parents_tail, i << 2UL | 1UL);
            child.parents_tail = i << 2UL | 1UL;

        } else {
            // 这些链接将不会被使用
            node.hi_prev = UINT32_MAX;
            node.hi_next = UINT32_MAX;
        }
        if (node.lo >= 0) {
            Node &child = table_[node.lo];
            node.lo_prev = child.parents_tail;
            node.lo_next = node.lo << 2UL | 2UL;
            plink_set_next(child.parents_tail, i << 2UL);

            child.parents_tail = i << 2UL;
        } else {
            // 这些链接将不会被使用
            node.lo_prev = UINT32_MAX;
            node.lo_next = UINT32_MAX;
        }
    }
    dp_mgr_ = make_unique<DpManager>(table_, num_var_);
}

/**
 * 计算上方向的选择路径
 * @param node_id 节点 ID。
 * @param up_id 上方向的 ID。
 * @param choice 存储选择路径的向量。
 * 计算从根节点到指定节点的选择路径。
 */
void ZddWithLinks::compute_upper_choice(int32_t node_id, count_t up_id,
                                        vector<uint16_t> &choice) noexcept {
    choice.clear();
    //    const int32_t root_id = table_.size() - 1;

    for (;;) {
        const Node &node = table_[node_id];
        assert(node.count_upper > 0);
        if (plink_is_term(node.parents_head)) {  // 根节点
            assert(node.count_upper > 0);
            break;
        }
        count_t offset = 0UL;

        plink_t plink = node.parents_head;
        for (;;) {
            const auto parent_id = plink_node_id(plink);
            const Node &parent = table_[parent_id];
            assert(parent.count_upper > 0);
            if (offset + parent.count_upper > up_id) {
                up_id = up_id - offset;
                node_id = parent_id;
                if (plink_is_hi(plink)) {
                    choice.emplace_back(parent.var);
                }
                break;
            } else {
                offset += parent.count_upper;
            }
            plink = plink_get_next(plink);
        }
    }
}

/**
 * 初始化上方向的选择路径
 * @param start_id 起始节点 ID。
 * @param visited 记录访问过的节点。
 * @param diff_choices 记录不同选择的索引。
 * @param diff_choice_ids 记录不同选择的节点 ID。
 * @param choices_buf 存储选择路径的缓冲区。
 * 初始化从根节点到指定节点的选择路径。
 */
void ZddWithLinks::compute_upper_initial_choice(
    const int32_t start_id, vector<uint32_t> &visited,
    vector<size_t> &diff_choices, vector<int32_t> &diff_choice_ids,
    vector<uint16_t> &choices_buf) noexcept {
    visited.clear();
    diff_choices.clear();
    diff_choice_ids.clear();
    int32_t node_id = start_id;
    for (;;) {
        const Node &node = table_[node_id];
        assert(node.count_upper > 0);

        if (plink_is_term(node.parents_head)) {
            assert(node.parents_head == node.parents_tail);
            break;
        }

        plink_t link = node.parents_head;
        auto previous_id = node_id;
        node_id = plink_node_id(link);
        assert(visited.empty() || table_[*(visited.rbegin()) >> 1].var > table_[node_id].var);
        if (plink_is_hi(link)) {
            visited.push_back(node_id << 1U | 1U);
        } else {
            visited.push_back(node_id << 1U);
        }
        if (link != node.parents_tail) {
            diff_choices.push_back(visited.size() - 1);
            diff_choice_ids.push_back(previous_id);
        }
    }
    size_t prev_choice = 0;
    for (auto idx : diff_choices) {
        trace2choice(make_reverse_iterator(visited.begin() + idx),
                     make_reverse_iterator(visited.begin() + prev_choice),
                     choices_buf);
        prev_choice = idx;
        batch_cover(choices_buf.cbegin(), choices_buf.cend());
        if (sanity_check_ && sanity()) {
            cerr << "inconsistent after batch cover in upper initial choice"
                 << endl;
            exit(1);
        }
    }
    trace2choice(visited.rbegin(),
                 make_reverse_iterator(visited.begin() + prev_choice),
                 choices_buf);
    batch_cover(choices_buf.cbegin(), choices_buf.cend());
    if (sanity_check_ && sanity()) {
        cerr << "inconsistent after batch cover in upper initial choice"
             << endl;
        exit(1);
    }
}

/**
 * 计算上方向的下一个选择路径
 * @param visited 记录访问过的节点。
 * @param diff_choices 记录不同选择的索引。
 * @param diff_choice_ids 记录不同选择的节点 ID。
 * @param choice_buf 存储选择路径的缓冲区。
 * @return 如果没有更多选择路径则返回 true，否则返回 false。
 * 计算从当前节点到下一个节点的选择路径。
 */
bool ZddWithLinks::compute_upper_next_choice(vector<uint32_t> &visited,
                                             vector<size_t> &diff_choices,
                                             vector<int32_t> &diff_choice_ids,
                                             vector<uint16_t> &choice_buf) {
    // 取消覆盖
    //    cerr << "update " << num_updates << endl;
    int var_prev = 100;
    for (const auto v : visited) {
        assert(table_[v >> 1].var < var_prev);
        var_prev = table_[v >> 1].var;
    }
    assert(diff_choices.size() == diff_choice_ids.size());
    while (!diff_choices.empty()) {
        size_t change_idx = *(diff_choices.rbegin());
        diff_choices.pop_back();
        uint32_t child_id = *(diff_choice_ids.rbegin());
        diff_choice_ids.pop_back();

        trace2choice(visited.rbegin(),
                     make_reverse_iterator(visited.begin() + change_idx),
                     choice_buf);
        batch_uncover(choice_buf.begin(), choice_buf.end());
        if (sanity_check_ && sanity()) {
            cerr << "inconsistent after batch uncover in upper next choice"
                 << endl;
            exit(1);
        }
        const auto val = visited[change_idx];
        visited.erase(visited.begin() + change_idx, visited.end());

        plink_t plink;
        plink_t ptail = table_[child_id].parents_tail;
        if (((val >> 1U) == plink_node_id(ptail)) &&
            ((plink_is_hi(ptail) && (val & 1U)) ||
             (!plink_is_hi(ptail) && !(val & 1U)))) {
            continue;
        }

        if (val & 1U) {
            plink = table_[val >> 1U].hi_next;
        } else {
            plink = table_[val >> 1U].lo_next;
        }
        if (plink_is_term(plink)) {
            print_parent_links(val >> 1U);
            print_parent_links(child_id);
            print_parent_links(plink_node_id(plink));
        }
        assert(!plink_is_term(plink));
        auto next_nid = plink_node_id(plink);
        assert(visited.empty() || table_[*(visited.rbegin()) >> 1].var > table_[next_nid].var);
        assert(table_[next_nid].count_upper > 0);
        if (plink_is_hi(plink)) {
            visited.push_back(next_nid << 1U | 1U);
        } else {
            visited.push_back(next_nid << 1U);
        }
        diff_choices.push_back(visited.size() - 1);
        diff_choice_ids.push_back(child_id);
        break;
    }
    if (diff_choices.empty()) {
        trace2choice(visited.rbegin(), visited.rend(), choice_buf);
        batch_uncover(choice_buf.begin(), choice_buf.end());
        if (sanity_check_ && sanity()) {
            cerr << "inconsistent after batch uncover in upper next choice"
                 << endl;
            exit(1);
        }
        visited.erase(visited.begin(), visited.end());
        assert(diff_choices.empty() && diff_choice_ids.empty());
        return true;
    }

    size_t prev_last_idx = *(diff_choices.rbegin());
    assert(prev_last_idx == visited.size() - 1);

    int32_t node_id = visited[prev_last_idx] >> 1U;
    for (;;) {
        const Node &node = table_[node_id];
        assert(node.count_upper > 0);

        if (plink_is_term(node.parents_head)) break;

        plink_t link = node.parents_head;
        int32_t previous_id = node_id;
        node_id = plink_node_id(link);
        assert(visited.empty() || table_[*(visited.rbegin()) >> 1].var > table_[node_id].var);
        if (plink_is_hi(link)) {
            visited.push_back(node_id << 1U | 1U);
        } else {
            visited.push_back(node_id << 1U);
        }
        if (link != table_[previous_id].parents_tail) {
            diff_choices.push_back(visited.size() - 1);
            diff_choice_ids.push_back(previous_id);

            trace2choice(visited.rbegin() + 1,
                         make_reverse_iterator(visited.begin() + prev_last_idx),
                         choice_buf);
            batch_cover(choice_buf.begin(), choice_buf.end());
            prev_last_idx = visited.size() - 1;
            if (sanity_check_ && sanity()) {
                cerr << "inconsistent after batch cover in upper next choice"
                     << endl;
                exit(1);
            }
        }
    }

    trace2choice(visited.rbegin(),
                 make_reverse_iterator(visited.begin() + prev_last_idx),
                 choice_buf);
    batch_cover(choice_buf.begin(), choice_buf.end());
    if (sanity_check_ && sanity()) {
        cerr << "inconsistent after batch cover in upper next choice" << endl;
        exit(1);
    }
    return false;
}

/**
 * 计算下方向的选择路径
 * @param node_id 节点 ID。
 * @param down_id 下方向的 ID。
 * @param choice 存储选择路径的向量。
 * 计算从根节点到指定节点的选择路径。
 */
void ZddWithLinks::compute_lower_choice(int32_t node_id, count_t down_id,
                                        vector<uint16_t> &choice) noexcept {
    choice.clear();

    while (node_id >= 0) {
        const Node &node = table_[node_id];

        count_t offset = node.count_hi;

        if (down_id < offset) {
            node_id = node.hi;
            choice.emplace_back(node.var);
        } else {
            node_id = node.lo;
            down_id = down_id - offset;
        }
    }
}

/**
 * 初始化下方向的选择路径
 * @param start_id 起始节点 ID。
 * @param visited 记录访问过的节点。
 * @param diff_choices 记录不同选择的索引。
 * @param choices_buf 存储选择路径的缓冲区。
 * 初始化从根节点到指定节点的选择路径。
 */
void ZddWithLinks::compute_lower_initial_choice(const int32_t start_id,
                                                vector<uint32_t> &visited,
                                                vector<size_t> &diff_choices,
                                                vector<uint16_t> &choices_buf) {
    visited.clear();
    diff_choices.clear();
    int32_t node_id = start_id;
    while (node_id >= 0) {
        const Node &node = table_[node_id];
        if (node.count_hi > 0) {
            visited.push_back(node_id << 1U | 1U);
            if (node.count_lo > 0) {
                diff_choices.push_back(visited.size() - 1);
            }
            node_id = node.hi;
        } else {
            assert(node.count_lo > 0);
            visited.push_back(node_id << 1U);
            node_id = node.lo;
        }
    }
    assert(node_id == DD_ONE_TERM);
    size_t prev_choice = 0;
    for (auto idx : diff_choices) {
        trace2choice(visited.begin() + prev_choice, visited.begin() + idx,
                     choices_buf);
        prev_choice = idx;
        batch_cover(choices_buf.cbegin(), choices_buf.cend());
        if (sanity_check_ && sanity()) {
            cerr << "inconsistent after batch cover in lower initial choice"
                 << endl;
            exit(1);
        }
    }
    trace2choice(visited.begin() + prev_choice, visited.end(), choices_buf);
    batch_cover(choices_buf.cbegin(), choices_buf.cend());
    if (sanity_check_ && sanity()) {
        cerr << "inconsistent after batch cover in lower initial choice"
             << endl;
        exit(1);
    }
}

/**
 * 计算下方向的下一个选择路径
 * @param visited 记录访问过的节点。
 * @param diff_choices 记录不同选择的索引。
 * @param choice_buf 存储选择路径的缓冲区。
 * @return 如果没有更多选择路径则返回 true，否则返回 false。
 * 计算从当前节点到下一个节点的选择路径。
 */
bool ZddWithLinks::compute_lower_next_choice(vector<uint32_t> &visited,
                                             vector<size_t> &diff_choices,
                                             vector<uint16_t> &choice_buf) {
    // 取消覆盖
    while (!diff_choices.empty()) {
        size_t change_idx = *(diff_choices.rbegin());
        diff_choices.pop_back();

        trace2choice(visited.begin() + change_idx, visited.end(), choice_buf);
        batch_uncover(choice_buf.begin(), choice_buf.end());
        if (sanity_check_ && sanity()) {
            cerr << "inconsistent after batch uncover in lower next choice"
                 << endl;
            exit(1);
        }

        visited.erase(visited.begin() + change_idx, visited.end());
        const auto val = visited[change_idx];
        if (val & 1U) {
            visited.push_back((val >> 1U) << 1U);
            diff_choices.push_back(visited.size() - 1);
            break;
        }
    }
    if (diff_choices.empty()) {
        trace2choice(visited.begin(), visited.end(), choice_buf);
        batch_uncover(choice_buf.begin(), choice_buf.end());
        if (sanity_check_ && sanity()) {
            cerr << "inconsistent after batch uncover in lower next choice"
                 << endl;
            exit(1);
        }
        return true;
    }

    int prev_last_idx = *(diff_choices.rbegin());
    int32_t node_id = visited[prev_last_idx] >> 1U;

    node_id = table_[node_id].lo;
    while (node_id >= 0) {
        const Node &node = table_[node_id];
        if (node.count_hi > 0) {
            visited.push_back(node_id << 1U | 1U);
            if (node.count_lo > 0) {
                trace2choice(visited.begin() + prev_last_idx, visited.end() - 1,
                             choice_buf);
                batch_cover(choice_buf.begin(), choice_buf.end());
                if (sanity_check_ && sanity()) {
                    cerr << "inconsistent after batch cover in lower next "
                            "choice"
                         << endl;
                    exit(1);
                }
                prev_last_idx = visited.size() - 1;
                diff_choices.push_back(visited.size() - 1);
            }
            node_id = node.hi;
        } else {
            assert(node.count_lo > 0);
            visited.push_back(node_id << 1U);
            node_id = node.lo;
        }
    }
    assert(node_id == DD_ONE_TERM);
    trace2choice(visited.begin() + prev_last_idx, visited.end(), choice_buf);
    batch_cover(choice_buf.begin(), choice_buf.end());
    if (sanity_check_ && sanity()) {
        cerr << "inconsistent after batch cover in lower next choice" << endl;
        exit(1);
    }
    return false;
}

/**
 * 隐藏指定的节点
 * @param node_id 要隐藏的节点 ID。
 * 隐藏指定的节点，更新父子链接。
 */
void ZddWithLinks::hide_node(const int32_t node_id) {
    Node &node = table_[node_id];
    //    cerr << "hide " << node_id << endl;

    if (!plink_is_term(node.parents_head)) {
        for (plink_t plink = node.parents_head;;  // !plink_is_term(plink);
             plink = plink_get_next(plink)) {
            int32_t parent_id = plink_node_id(plink);
            Node &parent = table_[parent_id];
            if (plink_is_hi(plink)) {
                parent.hi = node.lo;
            } else {
                parent.lo = node.lo;
            }
            if (plink == node.parents_tail) {
                break;
            }
        }
    }

    auto nhi = node.hi, nlo = node.lo;

    if (nhi >= 0) {
        auto hi_next = node.hi_next, hi_prev = node.hi_prev;
        plink_set_prev(hi_next, hi_prev);
        plink_set_next(hi_prev, hi_next);
    }
    if (nlo >= 0) {
        auto lo_next = node.lo_next, lo_prev = node.lo_prev;
        plink_set_prev(lo_next, lo_prev);
        plink_set_next(lo_prev, lo_next);
    }

    if (nlo >= 0 && !plink_is_term(node.parents_head)) {
        Node &lo_child = table_[nlo];
        auto np_head = node.parents_head, np_tail = node.parents_tail;
        plink_set_prev(np_head, lo_child.parents_tail);
        plink_set_next(np_tail, (nlo << 2UL) | 2UL);
        plink_set_next(lo_child.parents_tail, np_head);
        lo_child.parents_tail = np_tail;
    }
}

/**
 * 取消隐藏指定的节点
 * @param node_id 要取消隐藏的节点 ID。
 * 恢复指定节点的可见性，更新父子链接。
 */
void ZddWithLinks::unhide_node(const int32_t node_id) {
    Node &node = table_[node_id];

    auto nhi = node.hi, nlo = node.lo;
    if (nlo >= 0 && !plink_is_term(node.parents_head)) {
        Node &lo_child = table_[nlo];

        auto np_head = node.parents_head, np_tail = node.parents_tail;
        plink_t orig_lo_parent_head = plink_get_prev(np_head);
        plink_t orig_lo_parent_tail = plink_get_next(np_tail);
        plink_set_next(orig_lo_parent_head, orig_lo_parent_tail);
        plink_set_prev(orig_lo_parent_tail, orig_lo_parent_head);

        plink_set_prev(np_head, node_id << 2UL | 2UL);
        plink_set_next(np_tail, node_id << 2UL | 2UL);
    }

    if (nlo >= 0) {
        auto lo_next = node.lo_next, lo_prev = node.lo_prev;
        plink_set_prev(lo_next, node_id << 2UL);
        plink_set_next(lo_prev, node_id << 2UL);
    }

    if (nhi >= 0) {
        auto hi_next = node.hi_next, hi_prev = node.hi_prev;
        plink_set_prev(hi_next, node_id << 2UL | 1UL);
        plink_set_next(hi_prev, node_id << 2UL | 1UL);
    }


    if (!plink_is_term(node.parents_tail)) {
        for (plink_t plink = node.parents_tail;;  // !plink_is_term(plink);
             plink = plink_get_prev(plink)) {
            int32_t parent_id = plink_node_id(plink);
            Node &parent = table_[parent_id];
            if (plink_is_hi(plink)) {
                parent.hi = node_id;
            } else {
                parent.lo = node_id;
            }
            if (plink == node.parents_head) {
                break;
            }
        }
    }
}

/**
 * 隐藏cover_up类型的节点
 * @param node_id 要隐藏的节点 ID。
 * 隐藏cover_up类型的节点，更新父子链接。
 */
void ZddWithLinks::hide_node_cover_up(const int32_t node_id) {

    Node &node = table_[node_id];

    if (!plink_is_term(node.parents_head)) {
        for (plink_t plink = node.parents_head;;  //! plink_is_term(plink);
             plink = plink_get_next(plink)) {
            int32_t parent_id = plink_node_id(plink);
            Node &parent = table_[parent_id];
            if (plink_is_hi(plink)) {
                parent.hi = node.lo;
            } else {
                parent.lo = node.lo;
            }
            if (plink == node.parents_tail) break;
        }
    }

    if (node.lo >= 0) {
        auto lo_next = node.lo_next, lo_prev = node.lo_prev;
        plink_set_prev(lo_next, lo_prev);
        plink_set_next(lo_prev, lo_next);
    }

    if (node.lo >= 0 && !plink_is_term(node.parents_head)) {
        Node &lo_child = table_[node.lo];
        auto np_head = node.parents_head, np_tail = node.parents_tail;
        plink_set_prev(np_head, lo_child.parents_tail);
        plink_set_next(np_tail, (node.lo << 2UL) | 2UL);
        plink_set_next(lo_child.parents_tail, np_head);
        lo_child.parents_tail = np_tail;
    }
}

/**
 * 取消隐藏cover_up类型的节点
 * @param node_id 要取消隐藏的节点 ID。
 * 恢复cover_up类型节点的可见性，更新父子链接。
 */
void ZddWithLinks::unhide_node_cover_up(const int32_t node_id) {
    Node &node = table_[node_id];

    if (node.lo >= 0 && !plink_is_term(node.parents_head)) {
        Node &lo_child = table_[node.lo];

        auto np_head = node.parents_head, np_tail = node.parents_tail;
        plink_t orig_lo_parent_head = plink_get_prev(np_head);
        plink_t orig_lo_parent_tail = plink_get_next(np_tail);
        plink_set_next(orig_lo_parent_head, orig_lo_parent_tail);
        plink_set_prev(orig_lo_parent_tail, orig_lo_parent_head);

        plink_set_prev(np_head, node_id << 2UL | 2UL);
        plink_set_next(np_tail, node_id << 2UL | 2UL);
    }

    if (node.lo >= 0) {
        auto lo_next = node.lo_next, lo_prev = node.lo_prev;
        plink_set_prev(lo_next, node_id << 2UL);
        plink_set_next(lo_prev, node_id << 2UL);
    }


    if (!plink_is_term(node.parents_head)) {
        for (plink_t plink = node.parents_tail;;  //! plink_is_term(plink);
             plink = plink_get_prev(plink)) {
            int32_t parent_id = plink_node_id(plink);
            Node &parent = table_[parent_id];
            if (plink_is_hi(plink)) {
                parent.hi = node_id;
            } else {
                parent.lo = node_id;
            }
            if (plink == node.parents_head) break;
        }
    }
}

/**
 * 隐藏upperzero类型的节点
 * @param node_id 要隐藏的节点 ID。
 * 隐藏upperzero类型的节点，更新父子链接。
 */
void ZddWithLinks::hide_node_upperzero(const int32_t node_id) {
    Node &node = table_[node_id];
    assert(node.count_hi > 0);
    auto nhi = node.hi, nlo = node.lo;
    if (nhi >= 0) {
        auto hi_next = node.hi_next, hi_prev = node.hi_prev;
        plink_set_prev(hi_next, hi_prev);
        plink_set_next(hi_prev, hi_next);
    }

    if (nlo >= 0) {
        auto lo_next = node.lo_next, lo_prev = node.lo_prev;
        plink_set_prev(lo_next, lo_prev);
        plink_set_next(lo_prev, lo_next);
    }
}

/**
 * 取消隐藏upperzero类型的节点
 * @param node_id 要取消隐藏的节点 ID。
 * 恢复upperzero类型节点的可见性，更新父子链接。
 */
void ZddWithLinks::unhide_node_upperzero(const int32_t node_id) {
    Node &node = table_[node_id];
    if (node.lo >= 0) {
        auto lo_next = node.lo_next, lo_prev = node.lo_prev;
        plink_set_prev(lo_next, node_id << 2UL);
        plink_set_next(lo_prev, node_id << 2UL);
    }

    assert(node.count_hi > 0);

    if (node.hi >= 0) {
        auto hi_next = node.hi_next, hi_prev = node.hi_prev;
        plink_set_prev(hi_next, node_id << 2UL | 1UL);
        plink_set_next(hi_prev, node_id << 2UL | 1UL);
    }
}

/**
 * 隐藏lowerzero类型的节点
 * @param node_id 要隐藏的节点 ID。
 * 隐藏lowerzero类型的节点，更新父子链接。
 */
void ZddWithLinks::hide_node_lowerzero(const int32_t node_id) {
    Node &node = table_[node_id];
    if (!plink_is_term(node.parents_head)) {
        for (plink_t plink = node.parents_head;;  // !plink_is_term(plink);
             plink = plink_get_next(plink)) {
            int32_t parent_id = plink_node_id(plink);
            Node &parent = table_[parent_id];
            if (plink_is_hi(plink)) {
                parent.hi = node.lo;
            } else {
                parent.lo = node.lo;
            }
            if (plink == node.parents_tail) {
                break;
            }
        }
    }

    if (node.lo >= 0) {
        auto lo_next = node.lo_next, lo_prev = node.lo_prev;
        plink_set_prev(lo_next, lo_prev);
        plink_set_next(lo_prev, lo_next);
    }

    if (node.lo >= 0 && !plink_is_term(node.parents_head)) {
        Node &lo_child = table_[node.lo];
        auto np_head = node.parents_head, np_tail = node.parents_tail;
        plink_set_prev(np_head, lo_child.parents_tail);
        plink_set_next(np_tail,
                       (node.lo << PLINK_ADDR_OFFSET) | PLINK_IS_TERMINAL);
        plink_set_next(lo_child.parents_tail, np_head);
        lo_child.parents_tail = np_tail;
    }
}

/**
 * 取消隐藏lowerzero类型的节点
 * @param node_id 要取消隐藏的节点 ID。
 * 恢复lowerzero类型节点的可见性，更新父子链接。
 */
void ZddWithLinks::unhide_node_lowerzero(const int32_t node_id) {
    Node &node = table_[node_id];

    if (node.lo >= 0 && !plink_is_term(node.parents_head)) {
        Node &lo_child = table_[node.lo];

        auto np_head = node.parents_head, np_tail = node.parents_tail;
        plink_t orig_lo_parent_head = plink_get_prev(np_head);
        plink_t orig_lo_parent_tail = plink_get_next(np_tail);
        plink_set_next(orig_lo_parent_head, orig_lo_parent_tail);
        plink_set_prev(orig_lo_parent_tail, orig_lo_parent_head);

        auto plink_id = node_id << PLINK_ADDR_OFFSET | PLINK_IS_TERMINAL;
        plink_set_prev(np_head, plink_id);
        plink_set_next(np_tail, plink_id);
    }
    if (node.lo >= 0) {
        plink_set_prev(node.lo_next, node_id << PLINK_ADDR_OFFSET);
        plink_set_next(node.lo_prev, node_id << PLINK_ADDR_OFFSET);
    }

    if (plink_is_term(node.parents_head)) return;
    for (plink_t plink = node.parents_tail;;  // !plink_is_term(plink);
         plink = plink_get_prev(plink)) {
        int32_t parent_id = plink_node_id(plink);
        Node &parent = table_[parent_id];
        if (plink_is_hi(plink)) {
            parent.hi = node_id;
        } else {
            parent.lo = node_id;
        }
        if (plink == node.parents_head) {
            break;
        }
    }
}

/**
 * 检查DanceDD结构的有效性
 * @return 如果结构有效则返回 false，否则返回 true。
 * 检查DanceDD结构的完整性和一致性。
 */
bool ZddWithLinks::sanity() const {
    int pos, prev;

    bool has_error = false;

    for (pos = header_[0].right, prev = 0;;
         prev = pos, pos = header_[pos].right) {
        if (header_[pos].left != prev) {
            cerr << "Bad prev field at " << pos << endl;
            has_error = true;
        }
        if (pos == 0) break;

        uint64_t counter = 0ULL;

        int npos = header_[pos].down;
        int nprev = -1;

        for (;; nprev = npos, npos = table_[npos].down) {
            if (npos >= 0 && table_[npos].up != nprev) {
                cerr << "Bad up filed at node " << npos << endl;
                has_error = true;
            } else if (npos < 0 && header_[pos].up != nprev) {
                cerr << "Bad up filed at header " << pos << endl;
                has_error = true;
            }
            if (npos < 0) break;

            const Node &node = table_[npos];
            if (node.count_upper == 0 || node.count_hi == 0) {
                cerr << "Bad count at node " << npos << endl;
                has_error = true;
            }
            counter += node.count_upper * node.count_hi;

            // 检查父链接
            plink_t prev_link = npos << 2 | 2LU;
            for (plink_t plink = node.parents_head;;
                 prev_link = plink, plink = plink_get_next(plink)) {
                const auto &parent = table_[plink_node_id(plink)];
                plink_t back_link;
                if (plink_is_term(plink)) {
                    back_link = parent.parents_tail;
                } else if (plink_is_hi(plink)) {
                    back_link = parent.hi_prev;
                } else {
                    back_link = parent.lo_prev;
                }

                if (back_link != prev_link) {
                    cerr << "Bad parent links at " << npos << endl;
                    has_error = true;
                }

                if (plink == ((npos << 2LU) | 2LU)) {
                    break;
                }
                assert(!plink_is_term(plink));
                if (plink_is_hi(plink) && parent.hi != npos) {
                    cerr << "Bad parent hi at " << plink_node_id(plink) << endl;
                    has_error = true;
                } else if (!plink_is_hi(plink) && parent.lo != npos) {
                    cerr << "Bad parent lo at " << plink_node_id(plink)
                         << " node:" << npos << endl;
                    has_error = true;
                }
            }

            // 检查子链接
            if (node.lo >= 0) {
                const auto &child = table_[node.lo];
                if (node.var >= child.var) {
                    has_error = true;
                    cerr << "Child node " << node.lo << " has larger var than "
                         << npos << endl;
                }
                bool has_parent_link = false;
                if (!plink_is_term(child.parents_head)) {
                    for (plink_t plink = child.parents_head;
                         ;  // !plink_is_term(plink);
                         plink = plink_get_next(plink)) {
                        if (!plink_is_hi(plink) &&
                            plink_node_id(plink) == npos) {
                            has_parent_link = true;
                        }
                        if (plink == child.parents_tail) break;
                    }
                }
                if (!has_parent_link) {
                    cerr << "Child node " << node.lo
                         << " does not have parent link to " << npos << endl;
                    has_error = true;
                }
            }

            if (node.hi >= 0) {
                const auto &child = table_[node.hi];
                bool has_parent_link = false;
                if (node.var >= child.var) {
                    has_error = true;
                    cerr << "Child node " << node.hi << " has larger var than "
                         << npos << endl;
                }
                if (!plink_is_term(child.parents_head)) {
                    for (plink_t plink = child.parents_head;
                         ;  //! plink_is_term(plink);
                         plink = plink_get_next(plink)) {
                        if (plink_is_hi(plink) &&
                            plink_node_id(plink) == npos) {
                            has_parent_link = true;
                        }
                        if (plink == child.parents_tail) break;
                    }
                }
                if (!has_parent_link) {
                    cerr << "Child node " << node.hi
                         << " does not have parent link to " << npos << endl;
                    has_error = true;
                }
            }
        }

        if (counter != header_[pos].count) {
            cerr << "Count incosistent at header " << pos << endl;
            has_error = true;
        }
    }

    // 检查模型计数

    if (header_[0].right == 0) return has_error;

    int root_var = header_[0].right;
    int root_nid = header_[root_var].down;
    if (root_nid == -1) return has_error;

    {
        unordered_set<int32_t> reachable;
        stack<int32_t> stk;
        reachable.insert(root_nid);
        stk.push(root_nid);

        while (!stk.empty()) {
            const auto nid = stk.top();
            stk.pop();

            const auto &nde = table_[nid];
            if (nde.lo >= 0 && reachable.find(nde.lo) == reachable.end()) {
                reachable.insert(nde.lo);
                stk.push(nde.lo);
            }
            if (nde.hi >= 0 && reachable.find(nde.hi) == reachable.end()) {
                reachable.insert(nde.hi);
                stk.push(nde.hi);
            }
        }

        vector<int32_t> sorted_nodes(reachable.begin(), reachable.end());

        std::sort(sorted_nodes.begin(), sorted_nodes.end(),
                  std::greater<int32_t>());

        vector<count_t> dp_upper(table_.size(), 0UL);
        vector<count_t> dp_hi(table_.size(), 0ULL);
        vector<count_t> dp_lo(table_.size(), 0ULL);

        dp_upper[sorted_nodes[0]] = 1;

        for (int i = 0; i < sorted_nodes.size(); i++) {
            const auto nid = sorted_nodes[i];
            const Node &n = table_[nid];
            if (n.count_upper != dp_upper[nid]) {
                cerr << "Bad count upper at node " << nid << " "
                     << n.count_upper << ", " << dp_upper[nid] << endl;
                has_error = true;
            }
            if (n.lo >= 0) {
                dp_upper[n.lo] += dp_upper[nid];
            }
            if (n.hi >= 0) {
                dp_upper[n.hi] += dp_upper[nid];
            }
        }

        for (int i = sorted_nodes.size() - 1; i >= 0; i--) {
            const auto nid = sorted_nodes[i];
            const Node &n = table_[nid];
            if (n.hi == DD_ONE_TERM) {
                dp_hi[nid] = 1;
            } else if (n.hi >= 0) {
                dp_hi[nid] = dp_hi[n.hi] + dp_lo[n.hi];
            }
            if (dp_hi[nid] != n.count_hi) {
                cerr << "Bad count hi at node " << nid << " " << n.count_hi
                     << ", " << dp_hi[nid] << endl;
                has_error = true;
            }

            if (n.lo == DD_ONE_TERM) {
                dp_lo[nid] = 1;
            } else if (n.lo >= 0) {
                dp_lo[nid] = dp_hi[n.lo] + dp_lo[n.lo];
            }
            if (dp_lo[nid] != n.count_lo) {
                cerr << "Bad count lo at node " << nid << " " << n.count_lo
                     << ", " << dp_lo[nid] << endl;
                has_error = true;
            }
        }
    }

    return has_error;
}
