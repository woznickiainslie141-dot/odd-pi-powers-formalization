# π 的幂的无理测度：文献初查与 π³ 可行性评估

调查日期：2026-10-26。

## 判断

π³ 值得做一轮有明确退出条件的探索，但目前没有看到“稍改 π 的纪录积分便能突破”的证据。优先目标应是针对 π³ 的较小、显式、可验证的无理测度上界。证明上界有限本身已有一般理论；精确证明等于 2 则是另一个层级。

本轮未找到可以作为已确立的、专门优化的 π³ 最佳数值上界直接引用的文献。这个表述是检索结论，不是“这样的结果不存在”的证明。已核对关键原文段落；近期预印本的完整证明及其形式化补充未逐项独立审计。

## 1. 问题的准确边界

统一采用

\[
\mu(\xi)=\sup\{\nu:0<|\xi-p/q|<q^{-\nu}
\text{ 对无穷多个既约有理数成立}\}.
\]

非零有理数的倍乘不改变无理测度。因此

\[
\mu(\pi^{2m})=\mu(\zeta(2m)),\qquad
\mu(\pi^{2m+1})=\mu(\beta(2m+1)),
\]

其中

\[
\beta(s)=\sum_{j\geq0}\frac{(-1)^j}{(2j+1)^s},\qquad
\beta(3)=\frac{\pi^3}{32}.
\]

π³ 的自然特殊值对象是模 4 奇特征的 Dirichlet L 值，而不是 ζ(3)。奇偶差异确实影响适合的超几何构造、对称性和分母算术，但从对数幂及 Hermite–Padé 的角度仍有共同框架。π⁴ 等较高偶数幂的有效逼近也需要另外的工作，不能由 π² 的纪录自动得到。

即使已知 μ(π)=2，也不能直接推出 μ(π³)=2：把 p/q 立方只得到分母为 q³ 的特殊有理逼近，不能控制 π³ 的所有有理逼近。若只在有理立方这一受限集合中计量，分母高度改变后得到的指数也不是普通无理测度。

## 2. 已有结果与文献地图

| 文献 | 已核对的内容 | 对 π³ 的用途与限制 |
| --- | --- | --- |
| M. Waldschmidt, *Transcendence measures for exponentials and logarithms*, J. Aust. Math. Soc. 25 (1978), 445–465. [出版社](https://doi.org/10.1017/S1446788700021431) | 对指数、对数及相关数的定量超越估计。明确的 π 多项式下界也见下列 2025 论文表 1 对原文图 1、推论 4.2 的转述。 | 对固定 n 取多项式 qXⁿ−p，已经给出 μ(πⁿ)<∞。不是针对 π³ 优化的小常数纪录。 |
| *On the Existential Theory of the Reals Enriched with Integer Powers of a Computable Number*, STACS 2025. [正文](https://drops.dagstuhl.de/storage/00lipics/lipics-vol327-stacs2025/html/LIPIcs.STACS.2025.37/LIPIcs.STACS.2025.37.html) | 定义 3 明确多项式下界的高度约定；表 1 给出 π 的显式下界，参考文献 [33] 指向 Waldschmidt 1978。 | 可直接检查“所有固定幂有有限上界”的推导。这里使用的是正文转述的经典估计，未重审 1978 全文证明。 |
| W. Zudilin, *Two hypergeometric tales and a new irrationality measure of ζ(2)*, Ann. Math. Québec 38 (2014), 101–117. [原文](https://arxiv.org/abs/1310.1526) | μ(π²)=μ(ζ(2))<5.095412。 | 期刊基准；两套超几何表示与算术约消值得借鉴。这个数已不能无条件称为截至本调查日的最新预印本纪录。 |
| R. Marcovecchio, W. Zudilin, *Hypergeometric rational approximations to ζ(4)* (2019). [正文](https://arxiv.org/html/1905.12579) | 引言和末节给出 μ(π⁴)=μ(ζ(4))≤12.51085940…；核心包括新的分母控制。 | 很好的可行性参照：即使是偶数幂，已有快速逼近也可能不足以证明无理性，需要专门的算术改造。 |
| T. Rivoal, W. Zudilin, *Diophantine properties of numbers related to Catalan’s constant*, Math. Ann. 326 (2003), 705–721；W. Zudilin, *A few remarks on linear forms involving Catalan’s constant* (2002). [作者目录](https://rivoal.perso.math.cnrs.fr/articles.html)、[后者正文](https://arxiv.org/html/math/0210423v1) | β 值的超几何线性型、递推、置换群和分母性质。后者摘要明确主要研究正偶整数处 β 值。 | 是 β(3) 构造的重要邻近方法；不能把关于 β(2)、β(4) 等的定理直接改标成 π³ 上界。 |
| S. Fischler, T. Rivoal, *Multiple zeta values, Padé approximation and Vasilyev’s conjecture* (2013). [原文](https://arxiv.org/abs/1309.2534) | 讨论 Sorokin 1996 的 π² 超越测度构造，§5.3–5.4 明确对应的同时 Padé 问题及积分表示。 | 提供控制多个幂、消去额外常数的结构背景；本身不是 π³ 的优化数值纪录。 |
| G. V. Chudnovsky, *Irrationality exponents of logarithmic numbers: Values, quotients, and graded approximation*, 2026-10-20 预印本。 [正文](https://arxiv.org/html/2610.28079v1) | 定理 16.1：给定 n、ε，充分大的整数 b 使 logⁿ(1+1/b) 和 arctanⁿ(1/b) 的指数≤2+ε。定理 17.1 是小点的多项式版本。§19 区分受限幂类与普通指数。 | 最相关的新文献之一，但“小参数”门槛不能忽略。π/4=arctan(1) 不能直接代入充分大 b 的定理。正文也明确不延续 π 的幂的调查。 |
| E. Leibtag et al., *New Directions in Irrationality*, 2026-10-20 预印本。 [原文](https://arxiv.org/abs/2610.27799) | 定理 2 报告 μ(ζ(2))<4.62675、μ(ζ(3))<5.4197；定理 1 研究 ζ(3)、ζ(4) 的组合。 | CMF 框架可作为搜索递推/逼近族的新方法；已核对的定理未给出 π³ 的专门上界。 |

另外，D. N. Giraudin 的 2026-10-02 预印本 [A new upper bound for the irrationality exponent of ζ(2)](https://arxiv.org/abs/2610.02912) 给出 5.0193784，采用 Zudilin 两族构造的新参数。它说明旧积分族仍可能有可认证的优化空间；不能因此推断 π³ 也有现成同类族。

π 本身方面，OpenAI 的 [2026-09-24 预印本源文](https://github.com/openai/math/blob/main/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/main.tex) 陈述 μ(π)=2。本次仅核对了陈述和适用对象，没有独立验证整套证明，也没有用它推导 π³ 的上界。

## 3. “固定幂有有限测度”为什么已被覆盖

STACS 2025 表 1 给出如下经典估计的显式形式。若非零整系数多项式 P 的次数为 d、高度为 H≥16，则

\[
\log|P(\pi)|\geq
-2^{40}d(\log H+d\log d)(1+\log d).
\]

取 P(X)=qXⁿ−p。只考虑 |πⁿ−p/q|<1 的逼近时，H≤Cₙq。因此，对每个固定 n，有一个仅依赖 n 的正常数 cₙ，使

\[
\left|\pi^n-\frac pq\right|
\geq c_n q^{-[1+2^{40}n(1+\log n)]}.
\]

这给出一个极弱但有限的上界

\[
\mu(\pi^n)\leq1+2^{40}n(1+\log n).
\]

n=3 时右侧约为 6.922345840754×10¹²。这里只把它作为从文献显式公式直接导出的基线，不声称这是最佳通用结果，更不是 π³ 的当前纪录。

## 4. 一个针对 π³ 的最小试验：结构容易，算术困难

以下是本次调查中独立推导的初等例子，用于检验研究方向，不是声称新文献结果。

令

\[
I_N=\int_0^1
\frac{x^{2N}(1-x^2)^N}{1+x^2}(\log x)^2\,dx.
\]

在 y=x² 中作多项式除法：

\[
\frac{y^N(1-y)^N}{1+y}
=P_N(y)+\frac{(-1)^N2^N}{1+y},\quad
P_N\in\mathbb Z[y].
\]

利用

\[
\int_0^1x^{2j}(\log x)^2dx=\frac2{(2j+1)^3},\qquad
\int_0^1\frac{(\log x)^2}{1+x^2}dx=\frac{\pi^3}{16},
\]

得到

\[
16I_N=a_N+(-1)^N2^N\pi^3,\quad a_N\in\mathbb Q.
\]

例如 I₁=106/27−π³/8。该式通过数值积分交叉检查，50 位精度下残差约为 9.2×10⁻⁵²；其严格依据仍是上面的多项式除法和积分恒等式。

由于 x²(1−x²) 的最大值为 1/4，Laplace 法给出

\[
\log I_N=-N\log4+o(N).
\]

但 P_N 的次数为 2N−1，直接的分母清除数可取

\[
D_N=\operatorname{lcm}(1,3,5,\ldots,4N-1)^3,
\qquad \log D_N=12N+o(N).
\]

于是 16D_NI_N∈Z+Zπ³，其对数增长率是 12−log4>0。这种朴素清分母方式没有产生小的整数线性型。

这不是对所有改进族的否定，也没有排除最简分母远小于 D_N；它说明接下来必须改进分母估计、设计额外整除性、或改变积分族，不能只优化数值收敛速度。

## 5. 需要排除的一篇直接相关旧预印本

N. A. Carella, [Irrationality Exponents For Even Zeta Constants](https://arxiv.org/html/2003.01532)，arXiv:2003.01532，2020。

其定理 1.2、1.3 声称 π³ 及“小固定整数幂”的指数为 2。本次不将这些陈述视为成立的结论，理由可以具体定位：

引理 3.2 的证明从区间两端的函数值和连续性，推出整个区间内整数点的接近 1 的下界。连续性不提供这种控制；函数在区间内会振荡。

直接检验文中公式：取 k=3，π³ 的收敛分数 p/q=4930/159，v₂(q)=0，则

\[
x_N=\frac54\frac{159}{\pi^3}
=6.4099924685983984754\ldots,
\]

区间 [x_N−1/2,x_N+1/2] 包含整数 6。但

\[
|\sin(13\pi^4\cdot159)|
=0.0819094187103575283\ldots,
\]

而引理证明中式 (20) 后声称的下界是

\[
1-\frac{2\pi^2}{159^2}
=0.9992192077527716974\ldots.
\]

这两个区间在 45 位区间算术计算中完全分离。这个例子反驳的是证明中明确使用的下界；不将它说成对所有可能的渐近替代命题的反例。连续性论证本身也没有补上所需的渐近估计。故不能据该文把 π³ 的精确测度记作已知等于 2。

## 6. 推荐的入手顺序与成功条件

1. **先做 β(3) 的专门超几何/积分族。** 保持最终常数空间为 Q+Qπ³，并保留若干可调的分子、分母或移位参数。先求小指标的精确有理系数，计算真正公分母和公因子，筛掉只有数值精度、没有算术优势的族。
2. **同时评估分析与算术。** 设未清分母误差为 exp(−αN+o(N))，共同清分母代价为 exp(δN+o(N))，系数增长为 exp(βN+o(N))。首先需要 α>δ。再建立误差的双边渐近和足够的非退化/增长控制，才可用标准逼近引理得到形如

   \[
   \mu(\pi^3)\leq1+\frac{\beta+\delta}{\alpha-\delta}
   \]

   的上界。仅有误差上界或有限项实验还不够。
3. **把对数幂的 Hermite–Padé 作为第二路线。** 从 1、log z、(log z)²、(log z)³ 的同时逼近入手，在 z=i 或 −1 的指定分支上，研究能否消去低次幂并保留 Q+Qπ³。要计入消元、Gaussian 分母和取范数的成本；不能把幂乘或消元本身当作保留优良指数的保证。
4. **研究近期 CMF 方法是否提供合适初值。** 先证明候选递推的极限恰好是 β(3) 或 π³ 的有理变换，再做参数/轨迹搜索。已核对的 CMF 论文未直接提供这个终点。

评估：候选线性型的构造容易，产生有用的清分母后指数衰减属实质困难；获得一个较小显式上界是合理探索目标，直接要求 μ(π³)=2 不适合作为首轮成功条件。

检索方式：Firecrawl Research 的多种语义查询、参考文献/相似文献/引文扩展，配合英文及俄法关键词网页检索；对主要定理、参数门槛及有争议的证明步骤查阅正文。没有将未找到文献等同于不存在文献。
