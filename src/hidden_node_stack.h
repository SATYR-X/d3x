#ifndef HIDDEN_NODE_STACK_H_
#define HIDDEN_NODE_STACK_H_

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <stack>
#include <vector>
/**
 * A stack storing the node cells to hide.
 * this class helps to restore hidden nodes in an appropriate order.
 * 该类用于存储需要隐藏的节点，并帮助按适当顺序恢复这些节点
 */

class HiddenNodeStack {
   public:
    enum class HideType { UpperZero, LowerZero, CoverUp, CoverDown };
    // 表示隐藏节点的不同类型
   
    using stack_value_t = std::pair<int32_t, HideType>;
    // 栈中存储的值类型，包含节点 ID 和隐藏类型

    // 构造函数，初始化隐藏节点栈
    HiddenNodeStack();

    // 获取栈顶元素
    // 返回栈顶的节点ID和类型
    stack_value_t top() const { return *node_stack_.crbegin(); }

    // 移除栈顶元素
    void pop() { node_stack_.pop_back(); }

    // 将 CoverDown 类型的节点压栈
    // 输入需要隐藏的节点的ID
    void push_cover_down(const int32_t val) {
        node_stack_.emplace_back(val, HideType::CoverDown);
    }

    // 将 CoverUp 类型的节点压入栈
    // 输入隐藏节点的ID
    void push_cover_up(const int32_t val) {
        node_stack_.emplace_back(val, HideType::CoverUp);
    }

    /**
     * @brief 将 UpperZero 类型的隐藏节点压入栈。
     * @param val 需要隐藏的节点 ID。
     */
    void push_upperzero(const int32_t val) {
        node_stack_.emplace_back(val, HideType::UpperZero);
    }

    // 将 LowerZero 类型的隐藏节点压入栈。
    // param val 需要隐藏的节点 ID。
    void push_lowerzero(const int32_t val) {
        node_stack_.emplace_back(val, HideType::LowerZero);
    }

    /**
     * @brief 检查当前栈是否为空。
     * @return 若栈为空返回 true，否则返回 false。
     */
    bool is_empty() const {
        return node_stack_.size() == stack_start_positions_.top();
    }

    /**
     * @brief 创建一个新的检查点，用于恢复之前的隐藏状态。
     */
    void push_checkpoint() { stack_start_positions_.push(node_stack_.size()); }

    /**
     * @brief 反转当前栈段的顺序。
     */
    void reverse_current_stack() {
        std::reverse(node_stack_.begin() + stack_start_positions_.top(),
                     node_stack_.end());
    }

    /**
     * @brief 获取当前栈段的起始迭代器。
     * @return 返回常量迭代器，指向当前栈段的开始。
     */
    std::vector<stack_value_t>::const_iterator stack_cbegin() const {
        return node_stack_.cbegin() + stack_start_positions_.top();
    }

    /**
     * @brief 获取当前栈段的结束迭代器。
     * @return 返回常量迭代器，指向当前栈段的结束。
     */
    std::vector<stack_value_t>::const_iterator stack_cend() const {
        return node_stack_.cend();
    }

    /**
     * @brief 移除最后一个检查点。
     * @note 该操作需要确保栈为空，否则会触发断言失败。
     */
    void pop_checkpoint() {
        assert(is_empty());
        stack_start_positions_.pop();
    }

   private:
    std::vector<stack_value_t> node_stack_; // 存储隐藏的节点及其类型
    std::stack<int32_t, std::vector<int32_t>> stack_start_positions_;// 记录检查点位置
};

#endif  // HIDDEN_NODE_STACK_H_