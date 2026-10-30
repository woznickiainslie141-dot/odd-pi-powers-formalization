# N1_k3_search：定理 1.1 框架内压低 E_3 的数值搜索与 Arb 认证

（进行中，逐步更新。脚本目录：`improvement_plan/experiments/N1_k3_search/`）

## 0. 起点
- 已认证最好（主控代理）：k=3, L=99, t=0..27, ν=(64,4×27), m=171, E_3 < 1107.93 【arb_certified，日志 experiments/cert_L99.log】

## 1. 工具
- `cells.py`：整数版精确弧划分（与 code/certify.py 同一切点集 {k/d}、同一中点取样，但全部用公分母整数运算），
  行集约简为分量极小行（被支配行对 ν≥0 永不取到最小），相同极小行集的格合并（权重相加）。
  校验：L=69 十二层 E_3=1203.97244、L=14 两层 1762.60823、L=99 (64,4×27) E_3=1107.926786、γ=55.236264，
  与原稿/Arb 一致【float_numerical】。建表耗时 L=199、偏移 0..63：约 14 s（原 Fraction 版需数十分钟）。
- `scan2.py`：两级族 ν=(a,b×T) 批量扫描（矩阵乘 + reduceat 求 γ，Newton 求鞍点）。
- `localsearch.py`：整数局部搜索（单坐标 ±1..3 / 置零、成对转移 (+1,-1),(+1,-2),(+2,-1)、区间整体 ±1、随机扰动重启）。
- `certify_any.py`：certify_new.py 的扩展，接受任意 offsets/counts（含跳层），直接 import 原 code/certify.py 的 certify()（未修改）。

## 2. 进展（随时更新）
- L=69：局部搜索得 ν=(66,6×16,4×3)（t=0..19），m=173，E_3 浮点 1133.6402；
  Arb：E=[1133.64020158227921709839693646… ± 7.4e-60] < 1133.65 【arb_certified，日志 experiments/N1_k3_search/cert_L69.log】
- L=99：从 (64,4×27) 出发的局部搜索 + 10 次扰动未找到更优解（该点是所用邻域下的局部最优）【float_numerical】
- 两级族扫描（float_numerical，a∈[20,140]）：见第 3 节表格（待补全）。
