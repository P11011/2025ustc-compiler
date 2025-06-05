#include "DeadCode.hpp"
#include "logging.hpp"
#include <vector>
#include <unordered_set>

// 处理流程：两趟处理，mark 标记有用变量，sweep 删除无用指令
void DeadCode::run() {
    bool changed = false;
    func_info->run();
    do {
        changed = false;
        for (auto &f : m_->get_functions()) {
            auto *func = &f;
            changed |= clear_basic_blocks(func);
            mark(func);
            changed |= sweep(func);
        }
        sweep_globally();
    } while (changed);
    LOG_INFO << "dead code pass erased " << ins_count << " instructions";
}

bool DeadCode::clear_basic_blocks(Function *func) {
    bool modified = false;
    std::vector<BasicBlock *> blocks_to_remove;
    for (auto &bb : func->get_basic_blocks()) {
        if (bb.get_pre_basic_blocks().empty() && &bb != func->get_entry_block()) {
            blocks_to_remove.push_back(&bb);
            modified = true;
        }
    }
    for (auto *bb : blocks_to_remove) {
        bb->erase_from_parent(); // 不需要手动 delete，内部已处理
    }
    return modified;
}

void DeadCode::mark(Function *func) {
    marked.clear();
    work_list.clear();
    for (auto &bb : func->get_basic_blocks()) {
        for (auto &instr : bb.get_instructions()) {
            if (is_critical(&instr)) {
                marked[&instr] = true;
                work_list.push_back(&instr);
            }
        }
    }
    while (!work_list.empty()) {
        auto *curr = work_list.front();
        work_list.pop_front();
        mark(curr);
    }
}

void DeadCode::mark(Instruction *ins) {
    for (auto *operand : ins->get_operands()) {
        auto *def = dynamic_cast<Instruction *>(operand);
        if (!def)
            continue;
        if (def->get_function() != ins->get_function())
            continue;
        if (marked.count(def))
            continue;
        marked[def] = true;
        work_list.push_back(def);
    }
}

bool DeadCode::is_critical(Instruction *ins) {
    if (ins->is_ret() || ins->is_br() || ins->is_store() || ins->is_phi()) {
        return true;
    }
    if (ins->is_call()) {
        auto *callee = dynamic_cast<Function *>(ins->get_operand(0));
        // 如果调用的函数不是纯函数，不能删
        return !callee || !func_info->is_pure_function(callee);
    }
    // 被其他指令使用的，也不能删
    return !ins->get_use_list().empty();
}
bool DeadCode::sweep(Function *func) {
    std::unordered_set<Instruction *> to_remove;
    for (auto &bb : func->get_basic_blocks()) {
        for (auto &ins : bb.get_instructions()) {
            if (!marked.count(&ins)) {
                to_remove.insert(&ins);
            }
        }
    }
    for (auto *ins : to_remove) {
        // 移除所有操作数引用
        for (size_t i = 0; i < ins->get_num_operand(); ++i) {
            Value *op = ins->get_operand(i);
            if (op) {
                op->remove_use(ins, i);
            }
        }
        ins->get_parent()->remove_instr(ins);
        ++ins_count;
    }
    return !to_remove.empty();
}

void DeadCode::sweep_globally() {
    std::vector<Function *> unused_funcs;
    std::vector<GlobalVariable *> unused_globals;
    for (auto &f : m_->get_functions()) {
        if (f.get_name() != "main" && f.get_use_list().empty()) {
            unused_funcs.push_back(&f);
        }
    }
    for (auto &g : m_->get_global_variable()) {
        if (g.get_use_list().empty()) {
            unused_globals.push_back(&g);
        }
    }
    for (auto *f : unused_funcs) {
        m_->get_functions().erase(f->getIterator());
    }
    for (auto *g : unused_globals) {
        m_->get_global_variable().erase(g->getIterator());
    }
}
