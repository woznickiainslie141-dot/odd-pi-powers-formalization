# π³ 的一个显式无理测度上界

**历史版本说明（2026-10-31）：**本目录保留最初的平衡构造及其
2028.145383 上界。当前更强的 L99 结果为
μ(π³) ≤ 12970477737/11706979 < 1107.93，已通过 Lean 验收。
更新后的英文讲义、完整参数推导和验证范围见
`../odd_pi_powers_notes/main.pdf`（外层同名 PDF 也已同步）。
本稿的旧定理作为历史结果保留，不代表当前最佳项目结果。

主结果：μ(π³) ≤ E₍₂₈₉₎ < 2028.145383。

`main.tex` 包含完整的指数转移证明。外部分析输入是 Mignotte (1974)
第123页式(7)的经典余项估计和素数定理；整数性、非退化性、三次范数
及有理立方的例外情形均在文中证明。不作首次性或最佳纪录主张。

## 复算

在本目录运行：

```text
python code/certify_bound.py
python code/check_identities.py
xelatex -interaction=nonstopmode -halt-on-error main.tex
xelatex -interaction=nonstopmode -halt-on-error main.tex
```

第一个程序仅依赖 Python 标准库，使用精确有理区间认证小数上界；
第二个程序需要 SymPy，有限项验证只用来检查符号和归一化。
两个程序的结果位于 `data/`。

PDF 使用 XeLaTeX、ctex 和 Fandol 字体。完整证明以正文为准；
数值证书不单独证明所依赖的渐近分析。
