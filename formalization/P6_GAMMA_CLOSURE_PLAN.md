# P6 gamma closure: finite windows and tails

This is a read-only mathematical and implementation audit, not a proved
Lean result. The floating-point figures below are planning estimates computed
from `research/nested_pade_certificate_2026-10-27.json`; that file and its Arb
numbers are **not** proof evidence. No Lean, Lake, bounded runner, build,
generator, or axiom audit was run, and no existing source or cache was edited.

## What must be certified

For the `s=11`, `M=187`, `m=186`, `L=69` family, the candidate data give
`Y≈105.6505532331`, `D0≈605.8612949661`, `G0≈301.0322951390`, and scaled
`gamma≈45.4360013046` (base-shape rate `≈4.13054557314`). These are only
diagnostics. For a candidate one-sided lower divisor rate `γ`, the transfer
rates are `D=D0+γ`, `G=G0-γ`, and the planned exponent is

    186 * (D0 + G0) / (D0 - 2*G0 + 3*γ).

Using the candidate `D0,G0`, strict `<1203973/1000` requires approximately
`γ > 45.4359795516`, i.e. base rate `>4.13054359560`. The allowable loss
from the candidate base rate is only about `1.98e-6`; the accepted calibration
`2/69` cannot suffice. With independently proved rational bounds
`D0 ≥ 605.86129` and `G0 ≤ 301.03230`, a safe concrete target is base
`gamma ≥ 4.1305444`, scaled `γ ≥ 45.4359884`. Exact rational arithmetic then
gives a planned exponent below `1203.972898`, leaving about `0.000102` below
the required threshold. These decimal claims must all be replaced by proved
rational comparisons and an independently chosen rational `Y`; the quoted
candidate optimum is not a hypothesis or certificate.

## Existing accepted infrastructure

* `OddPiPowers.PrimeRates.periodGap`, `periodGap_eq_fraction`,
  `periodGap_nonneg`, and endpoint/period monotonicity are in
  `Arithmetic/FinitePeriodKernel.lean`.
* `CertifiedCellWindow` in `CellPrimeWindows.lean` needs **strictly interior**
  endpoints `cell.left < a < b < cell.right`. Its `toWindow`, `unit_bounds`,
  `rate_identity`, and `separated` establish valid prime windows and their
  contribution. `certifiedCellWindows_sum_le` proves the sum bound if labels
  `(period,cell)` are injective on the finite index set.
* `PrimeWindow.primes`, `mem_primes_quotient`, `sum_log_primes` in
  `PrimeWindowSums.lean`, and `finiteWindowRate` in `PrimeDivisorRates.lean`
  connect a **finite** window set to PNT and divide the sum of weighted
  reciprocal gaps by `L=69`.
* `twelveLayer_scaled_actualDivisor_eventually_exp_lower` in
  `ScaledPrimeRates.lean` applies the base windows to
  `twelveLayerShape.scaleWeights s`: the returned finite-window rate is
  multiplied by `s`, and the theorem applies to the actual prime divisor
  of any `ActualCarryGrouping`. A grouped `s=11` actual family remains an
  independent obligation. The theorem requires `1 ≤ 69*window.lower` for
  **each** window, an explicit `InjOn` label proof, and finite windows.
* The accepted fine table consists of **1180** open z-cells and **1166**
  positive rows, according to `P3B_CURRENT_CHECKPOINT.md`. A separate
  manuscript representation describes **571 merged positive intervals**;
  it must not be confused with the fine table, and merging across fine-cell
  endpoints is not automatically valid because the accepted lower function
  is zero at those endpoints. The current Pade JSON row has 1166 candidate
  nonzero cells. Prove an exact match to accepted rows or compute from the
  accepted table itself; do not assume JSON row correspondence.

## Strict interior windows and the cap

For each positive fine cell `c` choose one rational `δ>0`, for example
`δ=10^-16`, and use `a=c.left+δ`, `b=c.right-δ`. A kernel-checkable finite
table lemma must show all selected widths exceed `2δ`, and all positive
cells satisfy `c.left≥1/69`; candidate data indicate the first positive
left endpoint is `1/69`. Then for period `r=0` the cap holds because
`69*a≥1`, and for `r≥1` it holds trivially. Do not include an uncapped
period-zero cell left of `1/69`, even if it has positive candidate weight;
verify that exclusion against the actual table. Prove labels injective by
using an index type such as `(r, c)` with `c` a subtype of positive table
members, and `V(r,c).period=r`, `V(r,c).cell=c`. The strict shrink matters:
the theorem's windows cannot use the exact fine-cell endpoints, at which the
accepted lower bound is zero. Choosing very small rational δ does not make
the proof external or numerical: the value and endpoint inequalities can be
verified by ordinary rational arithmetic.

A convenient coarse shrink-error proof, for the prefix, bounds each affected
gap by at most `2*δ/(r+left)^2`. If every selected left endpoint is at least
`1/69`, every value is at most 17, and there are at most 1180 cells, the sum
over all `r≥0` is at most

    (2*δ/69) * 1180*17 * (69^2 + 2),

using `∑_{r≥1}1/r²≤2`. For `δ=10^-16` this is below `3e-10` in the base
rate. This bound itself and the table facts must be proved. Alternatively
certify the shrunken endpoints directly, avoiding any error lemma.

## Explicit finite-prefix + finite-tail lower bound

For a finite set of shrunken positive cells, write `w_c`, `a_c`, `b_c`, and
define the exact rational weighted width

    A = (1/69) * ∑_c w_c*(b_c-a_c).

At each period `r`, `0<a_c<b_c<1` and `periodGap_eq_fraction` give

    w_c/69 * periodGap r a_c b_c
      ≥ (w_c/69) * (b_c-a_c) / ((r+1)*(r+2)).

The inequality uses `(r+a_c)*(r+b_c) ≤ (r+1)*(r+2)` and positive
denominators. Consequently for `T<K` the **finite** tail `r=T,...,K-1`
is at least

    A * (1/(T+1) - 1/(K+1)).

This telescopes and gives a rigorous lower bound on the same finite window
family to which PNT applies. `K` is a fixed finite natural (e.g. 1,000,000),
not a second asymptotic limit and not an infinite sum passed through PNT.
Lean can quantify over `Finset.range K × positiveCells`, prove its rate via
finite-sum distribution and telescoping, and use a symbolic inequality for
the long tail; it need not enumerate or reduce the roughly billion windows.
However, the resulting huge finite set is a theorem-level construction:
avoid `decide`, `norm_num`, `rfl` or any proof step that unfolds all of it.

With *unshrunk candidate* cells, small read-only floating-point experiments
give `A≈0.0657844113781`. The following estimates are heuristic only:

| prefix periods `T` | prefix rate | prefix + telescoped tail, `K=10^6` |
|---:|---:|---:|
| 32 | 4.128488973 | 4.130482374 |
| 64 | 4.129517480 | 4.130529483 |
| 128 | 4.130031579 | 4.130541470 |
| 192 | 4.130202922 | 4.130543708 |
| 256 | 4.130288589 | 4.130544494 |

Thus `T=256` appears sufficient for the concrete rational target above,
whereas `T=128` is not. A useful proposed kernel certificate is
`prefix ≥ 4.13028858` and `A ≥ 0.0657844` for the **shrunken accepted rows**;
then exact rational arithmetic gives
`prefix + A*(1/257 - 1/1000001) > 4.1305444` with margin about `8.46e-8`.
The prefix threshold is about `9.49e-9` below the unshrunk candidate estimate,
so strict shrinking, rational rounding, and any mismatch with the accepted
table must together cost less than that; δ=`10^-16` has ample heuristic
room under the coarse shrink estimate. These two rational certificates have
not been computed or proved.

## A smaller prefix via a log/trapezoid tail

For `f_c(x)=1/(x+a_c)-1/(x+b_c)`, `x≥T≥1`, the function is positive,
decreasing and convex (`f''=2/(x+a)^3-2/(x+b)^3≥0`). The trapezoidal
inequality for convex functions would give the exact finite lower bound

    ∑_{r=T}^{K-1} f_c(r) ≥
      log((T+b_c)/(T+a_c)) - log((K+b_c)/(K+a_c))
      + (f_c(T)-f_c(K))/2.

This improves the `O(T^-2)` loss of the simple telescoping bound to roughly
`O(T^-3)`. Candidate floating-point estimates give total base rates
`4.130544760` at `T=24` and `4.130545187` at `T=32`, both above the
required candidate threshold. This could greatly reduce prefix work, but it
requires a new convex/trapezoid finite-sum theorem and certified one-sided
logs of rational arguments for up to 1166 cells. Existing `periodGap` lemmas
alone do not prove it. If certifying thousands of logarithms is expensive,
aggregate by a rational polynomial lower bound for `log(1+x)` and precompute
weighted rational moments, with a proved remainder; validate the direction
and the subtraction at `K`. Compare that cost to the purely rational `T=256`
route before choosing. Both methods still use finite prime windows.

## Practical kernel-certificate structure

1. Prove reusable symbolic lemmas for finite window indexing, cap/injection,
   shrinking, width sum, and the finite telescoped tail. Keep the PNT theorem
   applied to one finite `range K × cells`; exploit `Finset.sum_product` and
   algebraic identities rather than expanding the tail.
2. Certify the table-level facts and a lower bound for `A` in small blocks,
   reusing accepted table validity/order instead of re-proving 1180 cells.
   Avoid the 571 merged intervals unless a new pointwise theorem addresses
   fine-cell endpoints and `CertifiedCellWindow` separation explicitly.
3. For `T=256`, a direct exact sum has `256*1166=298496` cell-period terms.
   Avoid a single enormous rational denominator or one gigantic kernel
   reduction. A checker may certify per-cell or per-block fixed-denominator
   lower approximations: prove each rational contribution `≥ p/10^d` by
   cross multiplication, sum integer numerators, and use chunked proofs.
   To limit rounding below `1e-8`, termwise `d≥14` is enough, whereas
   per-cell rounding to `10^-11` costs at most `1.166e-8` and needs more
   digits or budget. Generator output is untrusted certificate data; every
   inequality and aggregation must be proved by Lean without native axioms.
4. Prove the selected fixed rational-height `D0`/`G0` bounds with ordinary
   one-sided log, atan and pi certificates. Reserve enough precision for
   the gamma margin and the final strict rational cross comparison; account
   for all sign conditions and eventual positive slack in the final transfer.

No actual gamma theorem, certificate acceptance, height theorem, complete
family, or final pi³ exponent is established by this note.

## Follow-up: fixed height `2113/20` and tighter gamma target

The main task supplied the rational height `Y=2113/20` and the candidate
one-sided goals `D0 ≥ 605861294/1000000`, `G0 ≤ 301032296/1000000`, and
scaled `gamma ≥ 4543599/100000`. The latter is equivalent to base
`gamma ≥ 4543599/1100000 = 4.1305445454545…`. These are still obligations,
not established bounds. Exact rational arithmetic conditional on them gives
`D ≥ 651.297284`, `G ≤ 255.596306`, a positive conservative gap
`D-2G ≥ 140.104672`, and the strict cross-comparison margin

    (1203973/1000)*(D-2*G) - 186*(D+G) ≥ 0.034521856 > 0.

For these stronger individual rate bounds the nominal rational exponent is
about `1203.9727536`. The candidate center calculation at the fixed height
is `D0≈605.8612949638465`, `G0≈301.0322951390135`: the proposed bounds
therefore leave less than `1e-6` room for each analytic certificate. Do not
reuse the more relaxed `D0/G0` and gamma example above as a proof of the new
target without recomputing its cross inequality.

The following **read-only candidate calculation** uses the 1166 positive
cells from JSON, with their weights divided by 11, and shrinks each endpoint
by exactly `δ=1/10^16`. It checks positive widths and `a≥1/69` for that
candidate data, using exact Python rational arithmetic. For each cell and
each prefix period, it rounds the exact positive contribution
`w*(b-a)/(69*(r+a)*(r+b))` down to a multiple of `10^-14`; the tabulated
prefix is the sum of those lower approximations. The width mean `A` is
computed exactly then rounded down to a multiple of `10^-12`. The tail uses
`K=1,000,000` and the exact rational telescoping formula above.

| `T` | rounded prefix lower candidate | rounded `A` | combined lower candidate | difference from new base target |
|---:|---:|---:|---:|---:|
| 256 | 4.13028858799660 | 0.065784411378 | 4.13054449268454 | -0.00000005277000 |
| 320 | 4.13033998647596 | 0.065784411378 | 4.13054485655261 | +0.00000031109806 |
| 384 | 4.13037425141582 | 0.065784411378 | 4.13054505423246 | +0.00000050877791 |

Thus the previous `T=256` suggestion is **insufficient for this new gamma
target**, even before attempting proof. `T=320` appears feasible, and
`T=384` leaves a safer margin. A simpler proposed pair of rational claims is
`prefix ≥ 4.13033998` at `T=320`, `A ≥ 0.065784411`, which together with
`K=1,000,000` implies base rate `>4.130544850075…` by exact rational
arithmetic. `K=100,000` is too small under this pair: its candidate lower
bound is about `4.130544258`, below the target.

Even though the planning computation used exact `Fraction` operations and
directed floors, it is **not** a kernel certificate: the candidate JSON has
not been proved identical to the 1166 accepted rows, the Python result has
not been checked in Lean, and no list of rounded terms was written or trusted.
At `T=320` the full per-term checker would handle `373120` terms, with total
rounding loss below `3.732e-9`; blockwise grouping and shared symbolic
estimates remain essential under the compiler cap. For `T=384` these figures
are `447744` terms and loss below `4.47744e-9`. A future certificate generator
may output proposed integer quotients for Lean to verify, but main must own
generator execution and prove every bound, including `A`, width, cap,
injection and exact comparison to the accepted cell table.

## Follow-up: rationalized trapezoid tail and merged arithmetic

The proposed rationalization is valid. For one strictly interior window
`0<a<b<1`, put `d=b-a`, `x=d/(T+a)`, `y=d/(K+a)`, with `1≤T<K`. In the
finite trapezoid lower bound above, use

    x - x²/2 ≤ log(1+x),       log(1+y) ≤ y.

Both hold for all nonnegative arguments. The second is an immediate
specialization of source-verified `Real.log_le_sub_one_of_pos` at `1+y`.
For the first, `Real.le_log_one_add_of_nonneg` gives the stronger lower bound
`2*x/(x+2)`, and

    2*x/(x+2) - (x-x²/2) = x³/(2*(x+2)) ≥ 0.

Thus the **per-cell finite tail lower bound is rational**:

    x - x²/2 - y + (periodGap T a b - periodGap K a b)/2.

Multiply by `w/69` and sum over the selected cells. The log expressions
occur only in the generic proof of soundness, not in numerical certificates.
One may use the slightly stronger `2*x/(x+2)-y+...` directly if its extra
denominator is convenient. The numerator `d` here is the *shrunken* width;
never confuse it with the original cell width when applying the formula.

The following candidate calculation uses the same 1166 JSON fine cells,
weights divided by 11, endpoint shrink `δ=10^-16`, and `K=1,000,000` as
the preceding section. Every prefix term and every rationalized tail term
was rounded **down** independently to a multiple of `10^-14` using exact
Python fractions. No terms were written or accepted as certificates.

| `T` | rounded prefix | rounded rational tail | sum | difference from `4543599/1100000` |
|---:|---:|---:|---:|---:|
| 16 | 4.12643075728707 | 0.00411230103819 | 4.13054305832526 | -0.00000148712929 |
| 24 | 4.12780307569498 | 0.00274168443606 | 4.13054476013104 | +0.00000021467649 |
| 32 | 4.12848897247951 | 0.00205621482243 | 4.13054518730194 | +0.00000064184739 |

`T=24` has a positive but narrow candidate margin; `T=32` gives substantially
more room. At `T=32` this is only `32*1166=37312` prefix terms plus 1166
tail terms, and the total downward rounding loss is at most `3.85e-10`.
These calculations do **not** prove the accepted Lean table has exactly the
candidate values, and the trapezoid theorem, rational checks, PNT application,
fixed-height analytic rate bounds and final transfer remain unproved.

Mathlib source inspection finds `convexOn_of_hasDerivWithinAt2_nonneg` and
`convexOn_of_deriv2_nonneg` in `Mathlib.Analysis.Convex.Deriv`. For
`f(t)=1/(t+a)-1/(t+b)` on `[T,K]`, positive denominators and `a<b` yield
`f''(t)=2/(t+a)^3-2/(t+b)^3 ≥ 0`; these lemmas can give `ConvexOn`.
`Mathlib.Analysis.Convex.Integral` offers Jensen-type `ConvexOn.map_integral_le`,
but this is the **opposite direction** from the required integral-versus-chord
inequality and does not by itself yield trapezoid soundness. The source file
`Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule` has
`trapezoidal_integral_one` and `sum_trapezoidal_integral_adjacent_intervals`;
the exposed `trapezoidal_error_le` is an absolute second-derivative error
bound, not an immediately located convex-sign lemma. Its import/cache cost
also needs checking by main.

A small direct proof can instead use the `ConvexOn` defining inequality on
each unit interval `[r,r+1]`: write `t=(1-u)r+u(r+1)` with `u=t-r` in
`[0,1]`, obtain `f(t)≤(1-u)f(r)+u*f(r+1)`, integrate using
`intervalIntegral.integral_mono_on`, and evaluate the affine chord integral
as `(f(r)+f(r+1))/2`. Sum and telescope endpoint contributions, then
evaluate the integral of the reciprocal difference as the two log differences
using positive denominators. This proves the required *finite* inequality;
it does not need a limiting Euler–Maclaurin theorem. Main must check actual
`ConvexOn` argument order, interval integrability, log-primitive formulas,
and `Finset` summation APIs with bounded compilation.

For reducing numeric checks, exact rational arithmetic may telescope
**unshrunk** adjacent fine cells with the same weight:
`periodGap r a b + periodGap r b c = periodGap r a c`. Read-only inspection
of this JSON row gives 1166 positive fine cells and 571 equal-weight merged
intervals. This count and merge relation must be verified against the accepted
table. The actual `CertifiedCellWindow` family remains the 1166 independently
shrunken fine cells; prove a separate explicit upper bound on the total
shrink loss and subtract it from the merged unshrunk numeric rate. No merged
prime-window pointwise or separation theorem is then needed. For the rational
tail, telescope the exact gap sums first and apply the generic rationalized
tail estimate to each merged **unshrunk** interval, not by asserting that
the nonlinear per-cell approximants telescope: `x-x²/2` is nonlinear in the
cell width. The combined unshrunk lower bound transfers to the actual fine
window rate only after the separately proved shrink-loss inequality. Check
also that the `r=0` cap applies to every actual fine window.
