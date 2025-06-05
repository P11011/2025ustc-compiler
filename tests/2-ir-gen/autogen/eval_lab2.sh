#!/bin/bash

# 显示用法说明
show_usage() {
    echo "Usage: $0 [options]"
    echo "Options:"
    echo "  none        - Run without optimization"
    echo "  dce         - Run with Dead Code Elimination"
    echo "  func-inline - Run with Function Inline"
    echo "  const-prop  - Run with Constant Propagation"
    echo "Example:"
    echo "  $0 dce func-inline      - Run with both DCE and Function Inline"
    echo "  $0 dce const-prop       - Run with both DCE and Constant Propagation"
    echo "  $0 dce func-inline const-prop  - Run with all optimizations"
    exit 1
}

# 如果没有参数，运行基础版本
if [ $# -eq 0 ]; then
    echo "Running without optimization..."
    python3 eval_lab2.py
    exit 0
fi

# 检查参数有效性并构建优化选项
opts=""
for arg in "$@"; do
    case $arg in
        "dce"|"func-inline"|"const-prop")
            opts="$opts $arg"
            ;;
        *)
            echo "Error: Invalid option '$arg'"
            show_usage
            ;;
    esac
done

# 运行带优化选项的测试
if [ -n "$opts" ]; then
    echo "Running with optimizations:$opts"
    python3 eval_lab2.py $opts
fi