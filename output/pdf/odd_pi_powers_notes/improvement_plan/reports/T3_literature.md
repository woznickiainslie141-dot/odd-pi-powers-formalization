# T3_literature：文献校准报告（进行中）

状态：初始化，正在检索。每条结论带状态标签；无法核实者标 unverifiable。

## 对照表（待填）

## 1. μ(π)、μ(π²) 历史与当前记录（待填）

### 已核实（第一批）
- [literature] Mignotte 1974 (Journées arithmétiques Grenoble 1973; Bull. SMF Mém. 37, 121–132; doi:10.24033/msmf.139; https://www.numdam.org/item/MSMF_1974__37__121_0/)：摘要（扫描第121页，本地副本 experiments/T3_literature/mignotte1974.pdf, mig-02.png）原文：|π-p/q| > q^{-20.6}（q>1）；|π²-p/q| > q^{-18}（q 充分大）。引言还宣布 |π-p/q|>q^{-20}（q≥q0 显式），并提到 π² 的逼近、整数对数的逼近、"代数数幂的同时逼近"，以及 tg 1。引言称 Mahler 1953 得 q^{-42}（q≥2），Mahler 指出可得 q^{-30}（q 充分大），Wirsing（未发表）得指数 21。
- [literature] Zeilberger–Zudilin, arXiv:1912.06345 (v2 2020-01-08)：μ(π) ≤ 7.103205334137… = 1+11.613890045331…/1.90291648559998…（https://arxiv.org/abs/1912.06345）。
- [literature] Salikhov：7.606308，Russian Math. Surveys 63 (2008) 570–572；详细版 Math. Notes 88 (2010) 563–573（ZZ 文献 [7][8]）。
- [literature] Zudilin：μ(π²)=μ(ζ(2)) ≤ 5.095412（5.09541178…），arXiv:1310.1526；Ann. Math. Québec 38 (2014) 101–117, doi:10.1007/s40316-014-0016-0（https://link.springer.com/article/10.1007/s40316-014-0016-0）。此前 Rhin–Viola 1996 5.441243（Acta Arith. 77, 23–56）。
- [literature, 2026 预印本，未经同行评审] Y. Bai, arXiv:2609.11276（2026-09-10/11）：μ(π) < 7.101862832357（ZZ 积分加两个分子指数 A1=A2=1857/2785）。https://arxiv.org/abs/2609.11276
- [literature, 2026 预印本] D. Niedbala Giraudin, arXiv:2610.02912（2026-10-02）：μ(ζ(2)) < 5.0193784；摘要提到 J. Kleid 于 2026-09 公开 5.0495243（机器检验证明；出处未给出 → unverifiable）。https://arxiv.org/abs/2610.02912
- [unverifiable] MathWorld/Wikipedia 提到 "OpenAI 2026 宣称 μ(π)=2"（GitHub openai/math，未经独立核实），以及 Leibtag et al. arXiv:2610.27799 宣称 ζ(2) 4.62675：均未核实，不应引用为已知结果。

### Mignotte 1974 逐页核对（扫描页 mig-03..mig-10.png，PDF 页码 2–9 对应期刊 p.122–129）
- [literature] p.122 式(1)–(4)：P=m!N^m(n!)^{m+1}，Q(z)=((z+1)…(z+n))^{m+1}，R_h(x)=(P/2πi)∮ z^h x^{z+n}/Q(z) dz = Σ_k A_hk(x)(log x)^k，A_hk∈Z[x]；p.123 式(7)：|R_h(e^{iα})| ≤ P/n^{n(m+1)}·2^{2(m+1)}(c+½)^m/(1+c²)^{m+1}·e^{6n²c(1+1/(4c))... }/π·exp(-(m+1)n(½log((c²+1)/4)-1))，c=|cot(α/(2(m+1)))|（指数部分的细节以扫描件为准）。与上一项目 pi3_explicit_bound 引用一致。
- [literature] p.124–125 Thm 1：取 x=i, m=5，c=7.595741…；|π-p/q|>q^{-20.6}（q≥2），|π-p/q|>q^{-20}（q≥exp(e^{110})）。注意：μ(π)≤20.6 确为该文结果（任务 2 的核实项）。
- [literature] p.126 Thm 2（π²）：x=-1, m=10，c=cot(π/22)，α = 4(1+(9+11log2)/((11/2)log((1+c²)/4)-9)) < 17.8，μ(π²) ≤ α。摘要写 q^{-18}（正文更精确 <17.8）。
- [literature] p.128 §V：(1) max_{1≤k≤5} ‖qπ^k‖ > q^{-3}（q>q1，显式）；(2) 若 ε_m 为使 max_{k≤m}‖qπ^k‖ ≤ q^{-1-ε} 有无穷多解的下确界，则 limsup ε_m log m ≤ 1+log 2；对 π² 同样成立。p.129 Thm 4：x 代数（度 δ）时 max_{k≤m}|(log x)^k - a_k| > (d^δ h^{δ-1})^{-1-(1+log2+ε)/log m}（a_k∈K 共同分母 d、高度≤h）。
- [proved（简单推理）] 这些都是"同时逼近"下界（所有 π^k 用同一分母同时逼近），不能推出单个 π³ 的无理测度：p/q≈π³ 并不给出 π、π² 的同分母好逼近。所以 Mignotte 1974 没有直接给出 μ(π³)；上一项目 2028.145 与本项目 1203.97 都是从其构造 (1)–(7) 出发自行做消元/范数转移得到的。

### 超越测度 / 代数逼近测度（第一批）
- [literature] Nesterenko–Waldschmidt, "On the approximation of the values of exponential function and logarithm by algebraic numbers", Mat. Zapiski 2 (1996) 23–42, arXiv:math/0002047（https://arxiv.org/abs/math/0002047 ，本地 experiments/T3_literature/math0002047.txt）。Thm 2(1)：ξ 实代数、d=deg ξ、L(ξ)≤L、L≥3 ⇒ |π-ξ| ≥ exp(-1.2·10^6·d·(log L + d log d)·(1+log d))；Thm 2(2)：|P(π)| ≥ exp(-2·10^6·d·(log L+d log d)(1+log d))。文中说明 Thm 2 的非显式形式最早由 Fel'dman [F 1951, 1960] 证明。
- [proved（由上述 Thm 2(1) 的直接推导）] 取 ξ=θ=(p/q)^{1/3}（qx³-p 的实根；若可约则 θ 有理，结论更强），d≤3，L(θ)≤p+q≈32q，|π³-p/q|=|π-θ|·|π²+πθ+θ²|≥|π-θ|·29 ⇒ μ(π³) ≤ 1.2·10^6·3·(1+log 3) ≈ 7.56·10^6（脚本: python 单行，见报告）。用 Thm 2(2) 直接取 P=qx³-p 得 ≈1.26·10^7。二者比本项目 1203.97 / 1107.93 差约 4 个数量级。
- [literature] Ю.М. Алексенцев (Aleksentsev), "О мере приближения числа π алгебраическими числами", Мат. заметки 66:4 (1999) 483–493；Math. Notes 66 (1999) 395–403, doi:10.1007/BF02679086（全文 https://www.mathnet.ru/php/getFT.phtml?jrnid=mzm&paperid=1191&what=fullt&option_lang=rus ，本地 aleksentsev1999.pdf / alek-01.png）。定理：d≥deg ζ, L≥L(ζ), L≥3，且 d 大于某个"充分大的有效常数" ⇒ |π-ζ| ≥ exp(-21.4708·d·(log L+d log d)(1+log d))。引言：Fel'dman 给出 γ·d(log L+d log d)(1+log d) 形式；文献[3]对充分大 d 取 γ=389，后有人宣布 γ=152。
- [heuristic] 由于 d 只需 ≥ deg ζ，可取 d=d0（那个有效常数），得 μ(π³) ≤ 21.47·d0(1+log d0)；但论文未给出 d0 的数值 → 数值 unverifiable。若（不合法地）直接代入 d=3，得 21.47·3·(1+log3)≈135；仅说明"插值行列式方法的形状"在小度数下若能做显式化可能有竞争力，不能作为已知结果引用。
- [结论, heuristic] 文献中没有找到任何"对固定 d=3 有显式数值"的 π 代数逼近测度能给出比 10^6 量级更好的 μ(π³)。目前能直接引用并推出数值的只有 Nesterenko–Waldschmidt 的 ≈7.56·10^6。
