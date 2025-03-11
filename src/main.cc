#include <math.h>
#include <unistd.h>

#include <chrono> // 用于计算运行时间
#include <unordered_set>

#include "dancing_on_zdd.h" // 包含ZDD相关的操作
#include "dp_manager.h"

/**
 * main function
 */

// extern uint64_t num_search_tree_nodes;
// extern uint64_t search_tree_depth;
// extern uint64_t search_tree_max_depth;
// extern uint64_t num_solutions;
// extern uint64_t ZddWithLinks::num_updates;
// extern uint64_t num_inactive_updates;

/**
 * get number of variables from zdd file
 * 获取ZDD文件中的变量数
 * 输入文件路径
 * 返回变量数量
 */
int get_num_vars_from_zdd_file(const string& file_name) {
    ifstream ifs(file_name);
    // 文件打开失败则打印错误信息并退出
    if (!ifs) {
        cerr << "can't open " << file_name << endl;
        exit(1);
    }

    string line;

    unordered_set<int> vars;// 用集合存储，避免重复

    while (getline(ifs, line)) {
        // 跳过以‘.’开头的行、空行或长度为0的行
        if (line[0] == '.' || line[0] == '\n' || line.size() == 0) continue;

        istringstream iss(line);
        int nid;
        int var;
        string lo_str;
        int lo_id;
        string hi_str;
        int hi_id;
        iss >> nid;// 读取节点ID
        iss >> var;// 读取变量ID

        vars.emplace(var);// 将变量ID存储到集合中
    }

    return vars.size();// 返回去重后的变量数量
}

// 显示用法并退出
void show_help_and_exit() {
    std::cerr << "usage: ./dancing_on_zdd_main -z zdd_file\n" << std::endl;
    exit(1);
}

int main(int argc, char** argv) {
    int opt;
    string zdd_file_name;
    int num_var = -1;
    // 解析命令行参数
    while ((opt = getopt(argc, argv, "z:h")) != -1) {
        switch (opt) {
            case 'z':
                zdd_file_name = optarg;// 读取 -z 参数之后的ZDD文件名
                break;
            case 'h':
                show_help_and_exit();// 读取失败就显示用法
                break;
        }
    }

    // 如果未提供ZDD文件名，则显示用法并退出
    if (zdd_file_name.empty()) {
        show_help_and_exit();
    }

    // 获取ZDD文件中的变量数
    num_var = get_num_vars_from_zdd_file(zdd_file_name);

    // 创建ZDD结构，并从文件加载数据
    ZddWithLinks zdd_with_links(num_var, false);
    zdd_with_links.load_zdd_from_file(zdd_file_name);

    // 进行一致性检查，失败则打印信息
    if (zdd_with_links.sanity()) {
        fprintf(stderr, "initial zdd is invalid\n");
    }
    fprintf(stderr, "load files done\n");

    // 用于存储搜索到的解
    vector<vector<uint16_t>> solution;

    // 记录开始时间
    auto start_time = std::chrono::system_clock::now();

    // 进行搜索
    zdd_with_links.search(solution, 0);

    // 记录结束时间
    auto end_time = std::chrono::system_clock::now();
    
    // 输出搜索结果，包括节点数、解的数量、更新次数和执行时间
    printf("num nodes %llu, num solutions %llu, num updates %llu, "
           "time: %llu msecs\n", ZddWithLinks::num_search_tree_nodes,
           ZddWithLinks::num_solutions, ZddWithLinks::num_updates,
           std::chrono::duration_cast<std::chrono::milliseconds>(end_time -
                                                                 start_time)
               .count());

    return 0;
}