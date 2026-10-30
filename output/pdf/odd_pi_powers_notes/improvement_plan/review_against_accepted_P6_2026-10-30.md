# Review of the improvement plan against accepted P6

Date: 30 October 2026. This is a mathematical and implementation review,
not acceptance of a new Lean theorem. P6 remains complete and unchanged.

## 1. What can actually be improved

The existing construction and most of its analysis can be retained. There
are two distinct changes: improving the transfer argument while keeping
the accepted arithmetic certificate, and changing the shape, which requires
a new arithmetic certificate.

| Route | Exponent or strict numerical target | Evidence and remaining obligation |
|---|---:|---|
| Accepted P6, twelve layers, m=186 | 1203.9727535995… | Accepted Lean theorem and executed axiom audit |
| Same P6 family, cofactor transfer | **1191.027** | Exact consequence of the new transfer lemma below and accepted P6 rates; the lemma is not yet formalized |
| L=69, twenty layers, m=173 | **1133.65** | Archived Arb certificate under the manuscript theorem; new finite certificate and Lean specialization needed |
| L=99, twenty-eight layers, m=171 | **1107.93** | Archived Arb certificate under the manuscript theorem; new finite certificate and Lean specialization needed |
| L=99 plus cofactor transfer | **1094.97** | The preceding certificate plus the new transfer lemma; neither application is yet Lean-accepted |
| L=129, m=170 | approximately 1093.580745 | Floating search output only |
| L=175, m=170 | approximately 1082.624182 | Floating search output only; the archived certification log stops after startup |

These are results within this project's construction. This review makes no
claim about the best bound in the current literature or global parameter
optimality.

The smallest mathematical extension of accepted P6 is the second row. Its
exact proposed exponent is

\[
 \frac{184}{186}\frac{42170551935}{35026168}
 =\frac{10429276285}{8756542}
 =1191.026810012445\ldots<1191.027.
\]

This improves the accepted exponent by about 1.08%. The L=99 parameter
change improves it by about 7.98%, and combining the two changes by about
9.05%.

## 2. A simpler proof of the T1 improvement

The correction in `reports/T1_elimination_theory.md` is substantive:
the worst-case elimination bound has **m+1-k**, rather than m, in its
numerator. The earlier statement in the main assessment that it exactly
recovers the old bound is inaccurate.

There is no need to formalize Gaussian lattices or successive minima to
obtain this modest improvement. Cofactors of a finite matrix suffice.

### Precise hypotheses

Fix an odd k at least 3 and m at least k. For every sufficiently large
n in a fixed progression L times the positive integers, suppose there are
m+1 polynomials U_h in Z[i][Z], of degree at most m, whose coefficient
matrix is invertible. Write lambda=i*pi/2. Assume, for every eta>0 and all
sufficiently large such n, uniformly in h and j,

\[
 |a_{h,j}|\le e^{(G+\eta)n},\qquad
 |U_h(\lambda)|\le e^{-(D-\eta)n},
\]

where G>0 and Delta=D-(k-1)G>0. A uniform divided-difference bound on
the disk of radius 2 follows from the coefficient bound, with a constant
depending only on m. P6 already supplies such a bound separately.

Under these hypotheses the proposed transfer conclusion is

\[
 \mu(\pi^k)\le
 \frac{(m+1-k)(D+G)}{D-(k-1)G}.
\]

Here the statement means the project's `ExponentUpperBound`, with its
usual epsilon slack. This review uses the safe range m>=k; the boundary
case m=k-1 is unnecessary for the applications and should not be added
without a separate treatment.

### Clearing denominators and choosing a nonzero combination

For an approximation p/q close to pi^k, put

\[
 Q=2^kq,\quad a=i^kp,\quad c=a/Q,\quad
 y=\frac{i}{2}(p/q)^{1/k},\quad
 d_r=\left\lfloor\frac{m-r}{k}\right\rfloor.
\]

Decompose

\[
 U_h(Z)=\sum_{r=0}^{k-1}Z^r V_{h,r}(Z^k),\qquad
 W_{r,h}=Q^{d_r}V_{h,r}(c)
 =\sum_{s=0}^{d_r}a_{h,ks+r}a^sQ^{d_r-s}.
\]

Every W entry is a Gaussian integer. The k evaluation functionals
P -> V_r(c) are independent: apply them to the monomials 1,Z,...,Z^{k-1}.
Invertibility of the coefficient matrix therefore implies that W has row
rank k. Select k columns giving a nonzero k by k minor.

Take the signed cofactors along its row r=0 and extend the resulting
vector by zeros to the other columns. This gives a vector x in Z[i]^(m+1)
such that

\[
 \sum_hW_{r,h}x_h=0\quad(1\le r<k),\qquad
 \sum_hW_{0,h}x_h\ne0.
\]

Thus the combination is guaranteed to be nonzero at y. It is not enough
merely to solve the homogeneous equations: that would leave open the
possibility of choosing a vector in the bad subspace.

Let sigma=sum_{r=1}^{k-1}d_r and S=d_0+sigma. Since |a|/Q is bounded
by a constant depending on k whenever |p/q-pi^k|<1, the cofactor formula
gives, uniformly in p,q,n,

\[
 \max_h|x_h|\le C_{m,k}Q^\sigma e^{(k-1)(G+\eta)n}.
\]

Counting all exponents 0,...,m by their residue modulo k proves exactly

\[
 S=\sum_{r=0}^{k-1}d_r=m+1-k.
\]

For m=186,k=3, the degrees are (62,61,61), sigma=122 and S=184.
In particular, the improvement comes from a new combination argument;
the original auxiliary polynomials still have degree 186.

### Small value, difference estimate and choice of scale

For U_x=sum_h x_h U_h, cancellation gives

\[
 U_x(y)=V_{x,0}(c)\ne0,\qquad Q^{d_0}U_x(y)\in\mathbb Z[i].
\]

Hence |U_x(y)|>=Q^(-d_0). The cofactor estimate and the original
remainder and height bounds give fixed constants C_1,C_2 such that

\[
 |U_x(\lambda)|\le C_1Q^\sigma e^{-(\Delta-k\eta)n},
 \qquad
 |U_x(\lambda)-U_x(y)|\le
 C_2Q^\sigma e^{k(G+\eta)n}|\lambda-y|.
\]

Choose 0<eta<Delta/k and n a sufficiently large multiple of L with

\[
 n=\frac{S\log Q+O(1)}{\Delta-k\eta}+O(L),
\]

so that the first bound is at most half Q^(-d_0). The integer lower
bound and the triangle inequality then imply

\[
 |\lambda-y|\ge C_3 Q^{-S}e^{-k(G+\eta)n}
 \ge C_4Q^{-E_\eta},\qquad
 E_\eta=\frac{S(D+G)}{\Delta-k\eta}.
\]

The constants are independent of p,q. For positive p/q near pi^k,
factorization of the difference of kth powers gives
|pi^k-p/q|>=2*pi^(k-1)*|lambda-y|. Approximations outside this
neighborhood are handled by a fixed lower bound. Letting eta decrease to
zero proves the stated exponent upper bound. Rounding to multiples of L
changes constants, not the exponent.

### Two repairs to make before general odd-power use

1. T1 uses `pi^k+1<2^(k+2)` to justify `|p|<=4Q`. That inequality fails
   for general large k. Use `|p|/Q <= (pi^k+1)/2^k`, a fixed k-dependent
   constant. The cofactor proof only needs that constant, so the exponent
   is unaffected. The displayed estimate happens to be valid for k=3.
2. A statement bounding gcd(Q,p) requires a reduced fraction hypothesis.
   The argument above does not need a gcd or a primitive polynomial and
   works for all p,q, matching the existing transfer interface.

## 3. What the Lean extension would actually involve

### Keeping the accepted twelve-layer family

Reuse the accepted construction, determinant, central remainder rate,
uniform disk and divided-difference bounds, sharp divisor rate, and P6
rational numerical bounds. Do not change those accepted sources.

The additional work is finite algebra and the transfer assembly:

1. Residue-class decomposition and denominator-cleared evaluation in Z[i].
2. A nonzero-minor/cofactor selection lemma, with an explicit norm bound.
3. The identity sum d_r=m+1-k, and the nonzero Gaussian integer lower bound.
4. The rounded-scale argument with S replacing m in its q-exponent.
5. A new transfer theorem and the fixed P6 application, followed by guarded
   compilation and an audit of the new dependency closure.

For a short first implementation, specialize the cofactor step to k=3:
only a 3 by 3 minor and 2 by 2 cofactors are required. A later generic
k version would reuse the same proof structure.

Relevant existing interfaces include:

- `Analysis/ActualReducedDiskHeight.lean`:
  `reduced_complexPolynomial_coeff_bound` already bounds every coefficient
  by `actualReducedHeight`.
- `Analysis/ActualHeightRate.lean` and `Analysis/ActualReducedRates.lean`:
  their majorant and quotient estimates give the corresponding exponential
  coefficient bound. A thin exported lemma is needed; the current
  `AuxiliaryFamily` record exposes disk bounds rather than this coefficient
  bound directly.
- `Transfer/NonzeroRow.lean`: coefficient matrix and determinant interfaces.
- `Transfer/RateComparison.lean`: rounded indices and exponential comparisons.
- `Transfer/TwelveLayerPiCube.lean`: the accepted family and rational rates
  used by the final specialization.

This is a contained extension, but changing `186` to `184` in the call to
the old `irrationality_transfer` is invalid: its parameter also specifies
the degree and number of rows.

### Changing to L=99

At the level of the manuscript, this is a parameter change. The general
construction and analytic rate estimates already support other shapes.
The present Lean finite arithmetic layer, however, has twelve-layer
specializations: L=69, 24 endpoints, 1180 cells, a base weight bound 17,
and specialized period/window and carry-grouping constants.

The L=99 candidate has offsets 0,...,27 and counts (64,4,...,4), with
M=172, m=171, 56 endpoints and 3004 critical cells in the archived
partition. A base shape (16,1,...,1) scaled by 4 is convenient.
These new cells cannot be certified by the old twelve-layer table.
The checker and window estimates should be generalized or given new
additive specializations, then supplied with newly checked data.

Even the improved twenty-layer L=69 case needs a new table: its partition
has 1470 cells and 40 endpoints. Keeping L alone does not retain the
old arithmetic certificate.

For a Lean application it is also preferable to certify a nearby fixed
rational height rather than import the archived saddle interval. For
L=99, 1801/20 is a natural candidate; its numerical inequalities still
need their own executed checks. No such new check succeeded in this review.

## 4. Computation and provenance in this review

Executed:

- Exact rational comparison of the accepted P6 exponent multiplied by
  184/186, yielding 10429276285/8756542<1191.027.
- Exact rational parsing of the archived L=69 and L=99 Arb intervals;
  checks of parameter admissibility, positive gaps, consistency of E
  with D and G, and strict comparisons after multiplying by (m-2)/m.
  The resulting proposed combined values are 1120.53453451196… and
  1094.96857823018…, respectively.
- Inspection of the current accepted Lean interfaces and the unfinished
  L=175 certification log.

Records:

- `experiments/p6_review_2026-10-30/exact_p6_comparison.json`
- `experiments/p6_review_2026-10-30/archived_interval_audit.json`
- Reproduction helper: `scripts/review_improvement_plan.py` at project root.

The helper's `--audit-archives` mode performs the small exact consistency
check. Its `--replay L99 L129 L175` mode uses isolated sequential Windows
jobs capped at 1536 MiB and 240 seconds each, retaining the existing
startup memory gates. Launch was refused for insufficient free physical
RAM; no child replay or compiler started. Therefore this review does not
claim to have independently recomputed the archived arc minima or Arb
transcendental bounds. No accepted Lean source, toolchain, cache or memory
limit was changed.

## 5. Recommended order and realistic reach

For the smallest extension of the accepted proof, implement the k=3
cofactor transfer and target **1191.027**, retaining all P6 finite data.
For the larger numerical improvement, follow with a reusable finite
certificate interface and the L=99 application, targeting **1094.97**
with the new transfer, or **1107.93** with the existing transfer.
Recheck L=129 and L=175 numerically before choosing an even larger table.

For higher odd powers the same cofactor theorem improves the old exponent
by the factor (m+1-k)/m. For the manuscript's large values of m this is a
small relative improvement and does not change the exponential growth
rate in k. Shape optimization remains the more relevant numerical lever.

The proposed short-vector/balanced-minima route to an exponent around
10–100 remains a research question. Cofactors prove the worst-case bound;
they do not prove that stronger balanced estimate. With G>0 the new
exponent is greater than m+1-k, so the present m=186 and m=171 families
cannot reach below 100 by this transfer change, even with arbitrarily
favorable rate ratios. This is an obstruction for these fixed degrees,
not a proof that every possible shape or new construction fails.
