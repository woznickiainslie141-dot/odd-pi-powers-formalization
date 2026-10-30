# P3-A：实际辅助多项式的素数幂整除与可约去公因子

## 1. 目标与边界

在现有已闭合 P1、P2 上，证明稿件第 3 节的局部素数算术估计，将它接到**实际的** `actualAuxiliaryInt` 系数，构造明确的公共整数因子，定义约去因子后的整数多项式，并证明在 i 处的矩阵仍非退化。

本目标仅为 P3-A，不连跑后续阶段。以下不属于本次完成条件：

- 圆周零弧、连续参数单元、中点检查器的正确性（P3-B）。
- 素数定理依赖、公共因子的指数增长率 gamma（P4）。
- 系数增长率、完整轮廓分析、Stirling/黎曼和（P5）。
- 任何四个具体无理测度数字或一般奇数幂的参数代入（P6–P7）。

避免将“有公因子”误说成“已经改善指数上界”：本阶段不证明因子的渐近增长率。

## 2. 基线与已验收对象

工程目录：`formalization/OddPiPowers/`。维持 Lean/Mathlib v4.35.0 与锁定 manifest。

阅读：

1. `docs/STATUS.md`、`docs/LUNA_HANDOFF.md`、`docs/PROOF_GAPS.md`。
2. `OddPiPowers/Construction/ActualAuxiliary.lean` 中相关定义与最终声明。
3. `OddPiPowers/Construction/LocalDenominators.lean`。
4. 稿件 `output/pdf/odd_pi_powers_notes/sections/03_arithmetic.tex`（相对于工作区）。

P2 的实际对象如下，禁止另建一套没有证明对应关系的多项式：

- `P : ActualIntervals M`，其中 `n=P.n`，左端点非降，`2*left[a] ≤ n`。
- `right[a]=n-left[a]`，`length[a]=n-2*left[a]`。
- `P.interval a`、`P.multiplicity ell`、`P.poleIndices ell`、`P.regularIndices ell`。
- `P.poleLocalFactor a ell`：带符号二项式常数乘正规化倒数线性因子的乘积。
- `P.regularLocalFactor a ell`：整数权部分分式和。
- `P.localExpansion ell h`：整数局部多项式分子与全部局部因子的乘积。
- `P.localCoefficient ell h j`：提取阶数 `multiplicity(ell)-1-j`，不够阶时为零。
- `auxiliaryScale M n j = (M-1)! * intervalLcm(n)^(M-1) / j!`。
- `actualAuxiliary P h j : Q[X]`、`actualAuxiliaryInt P h j : Z[X]`。
- `map_actualAuxiliaryInt` 已证明二者一致。
- `actualAuxiliaryPolynomialDet_factorization` 与
  `actualAuxiliaryPolynomialMatrixAtI_det_ne_zero` 已闭合。

P2 把区间阶乘放在 `localFactor` 内，`auxiliaryScale` 不再重复乘它们；不能套用旧归一化时再乘一次区间阶乘。

基线核查记录见 `P2_REVIEW_2026-10-27.md`。重新构建与审计后再开始修改。不要重做 P1/P2，也不要为了统一风格重写其 3000 多行证明。

## 3. 数学目标 A：有符号取整进位

固定素数 p，满足

    p ≤ n,  n < p^2.

这等价于稿件使用的 sqrt(n)<p≤n，形式化时优先使用整数平方条件。

对 0≤ell≤n，定义每个区间的进位：

    w[a](p,ell)
      = floor(length[a]/p)
        - floor((ell-left[a])/p)
        - floor((right[a]-ell)/p).

后两个分子可能为负。建议直接用正除数下的 `Int` 欧几里得除法表达这些 floor，避免额外引入实数取整；必须证明其确为所需的有符号公式。

证明 `w[a]` 只能为 0 或 1，再定义其自然数版本以及

    W(p,ell) = sum[a : Fin M] w[a](p,ell).

不能一开始把负数截断成自然数，也不能先取 `toNat` 再使用尚未证明的非负性。

建议单独建立可复用引理：对整数 x,y 和正整数 p，

    (x+y)/p - x/p - y/p ∈ {0,1}.

实际应用中的 x+y 等于区间长度。

## 4. 数学目标 B：局部系数的素数估计

使用现有有理赋值 API 或 p-整有理数子环，选择一种路线完成。不要同时开发多套表示而不连接。

若使用 `padicValRat`，先检查其在零处的约定。所有可能为零的系数应使用

    coefficient = 0 OR valuation(coefficient) ≥ bound

或等价的安全整除/局部整性命题；禁止把返回数值 0 的 API 当成在零处返回正无穷。

### 4.1 非零距离与 lcm

证明对非零整数距离 e、|e|≤n，有 v_p(e)≤1；对 `intervalLcm n`，有 v_p=1。

可复用现有的有限 lcm 赋值定理或最大素因子指数性质。不需要为此导入或证明素数定理。

### 4.2 极点因子

当 ell 在区间中，局部常数为已证明的带符号二项式系数，赋值恰为 w[a]。利用 n<p^2，阶乘赋值的高阶项全部消失。

证明其 u 阶系数非零时，赋值至少

    w[a]-u.

其余线性因子对应的非零距离每次至多损失一阶 p 赋值。

### 4.3 正则因子——本目标的主要难点

当 ell 不在区间内，需要证明常数的赋值为

    w[a]-1,

而 u 阶系数的赋值至少 `w[a]-1-u`。

不要直接对整数权部分分式和做一个粗糙逐项估计，然后假定它保留所需的 w[a]。建议利用 P2 的

    regularLocalFactor_mul_localDenominator

把实际正则因子转写成“常数乘正规化倒数因子乘积”，再计算常数。两侧得到相同分母乘积时，应利用非零/单位性严格取消。

若 ell<left[a]，令 s=left[a]-ell>0，常数为

    length[a]! * (s-1)! / (s+length[a])!.

另一侧有一个符号单位，赋值不变。关键有符号恒等式为

    floor((s-1)/p) = -floor(-s/p)-1.

参与这些阶乘的参数均不超过 n，需要明确证明后才能使用 n<p^2 的简化。

### 4.4 乘积与卷积

设 mu=P.multiplicity ell、m=M-1。提取局部阶数至多 `mu-1-j`，正则因子数是 `M-mu`。证明乘积系数的统一估计，不跳过卷积分拆或求和可能等于零的情况。

乘上 `intervalLcm(n)^m` 后，预算抵消为

    m + W(p,ell) - (M-mu) - (mu-1-j) = W(p,ell)+j.

整数多项式分子 `(-ell+w)^h` 与整数 `m!/j!` 不降低这一界。m 可以大于 n；不应额外假设 p>m，除非发现必要性并明确说明其对原目标的影响。

## 5. 数学目标 C：接入实际整数系数

优先证明强局部声明，名字可自选：

    (p : Z)^(W(p,ell)+j.val)
      divides (actualAuxiliaryInt P h j).coeff (P.n-ell)

假设只有 p 为素数、p≤n、n<p^2、ell≤n，以及 h,j 的合法索引。

必须从 `map_actualAuxiliaryInt` 与实际局部系数表达式完成桥接，不能把目标换成一个尚未识别为该整数系数的有理表达式。

若所选接口更便于先证明标准弱界 p^W 整除，可以先完成它，再恢复额外的 j。最终尽量交付强界；若强界确实需要改动，说明精确原因，不能静默删掉它。

对 k>n 的整数多项式系数，使用 P2 次数界证明为零。对 k≤n，选择 ell=n-k，并严格处理自然数减法。由此取得对所有次数 k 的系数整除。

## 6. 数学目标 D：明确的公共因子和商多项式

定义一个确切的有限极点最小值：

    e_p(P) = min[0≤ell≤n] W(p,ell),
    Pi(P) = product[prime p≤n, n<p^2] p^(e_p(P)).

最小值所取集合始终非空（包含 ell=0）。可以用 `Fin(n+1)` 或非空 Finset 的最小值；不需要连续圆周最小值。

证明：

1. Pi 是正自然数。
2. 不同素数的相应幂互素。
3. Pi 整除每个 `actualAuxiliaryInt P h j` 的每个整数系数。
4. 构造 `reducedAuxiliaryInt P h j : Z[X]`，证明

       C(Pi(P))*reducedAuxiliaryInt P h j = actualAuxiliaryInt P h j.

   可按整数系数精确相除定义。存在性和乘回恒等式必须证明。

5. 将商多项式在 i 处的实际矩阵定义出来，证明其行列式非零。由非零 Pi 与 P2 的非零行列式推出，不能在定义里附加非零假设。

允许先在 Q/Complex 层完成矩阵缩放，再通过整数商的映射证明其确为实际商矩阵。没有必要在本目标中提前生成完整 `AuxiliaryFamily`，因为它还缺分析估计。

## 7. 必须包含一个非平凡实例

使用一个小但能检测负数除法和正则因子的实例：

    M=2, n=42, left=(0,3), intervals=[0,42],[3,39], p=41.

核验 p 为素数、p≤n、n<p^2，并证明所有 ell=0,...,42 满足 W(41,ell)≥1，从通用定理推出 41 整除所有实际辅助整数多项式的系数。

这个实例在区间外两侧都会调用负数取整，并且证明公共因子不是恒等于 1 的空构造。

不必展开整个辅助多项式或计算巨大的有理部分分式。应检查有限进位表，然后应用通用系数整除定理。`actualAuxiliaryInt` 使用选择定义，不适合当成可执行表达式直接 `decide` 求值。

有限进位表可以使用内核可核验的有限计算。外部 Python 可作调试，但不能代替 Lean 证明，也不要引入原生评估公理作为最终可信基础。

## 8. 建议的文件与接口

保持 P2 大文件稳定，新增选择性导入的算术模块，例如：

    Arithmetic/SignedCarry.lean
    Arithmetic/LocalPrimeValuation.lean
    Arithmetic/ActualCoefficientDivisor.lean
    Arithmetic/ReducedAuxiliary.lean
    Arithmetic/PrimeDivisorExample.lean

名称可调整，范围不要扩张成完整 p-adic 理论建设。先调查已有 API，再选用能处理负指数和零的精确接口。

将关键声明加入库根与 `AxiomAudit.lean`。不要引入 `Mathlib.Tactic` 全量导入，避免大量冷编译；复用已有锁定环境，按需要取少量缓存。

## 9. 验收与状态更新

完成必须同时满足：

- 进位 0/1、极点与正则因子赋值、卷积预算均为普遍定理。
- 结论落在实际 `actualAuxiliaryInt` 上。
- 有明确定义的正整数 Pi、整数商及非退化性。
- n=42,p=41 的非平凡实例通过。
- 完整构建通过，关键定理的 transitive axioms 没有 sorryAx 或新增数学/数值公理。
- 更新 STATUS、BLUEPRINT、PROOF_GAPS 与 LUNA_HANDOFF，记录准确的新接口。

允许沿途保存闭合模块，但最终不能把“已定义公式”“把赋值结论写成假设”或有限实例冒充 P3-A 的普遍证明。

若发现实际数学错误，应报告最小失败命题、具体参数、对后续原上界的影响及可能修复；不要继续改写目标来掩盖失败。

阶段完成后停止并交付，不自动继续 P3-B、P4 或 P5。下一步可再单独指定“连续单元证书”或“公共因子速率”，保持每轮投入可验收。
