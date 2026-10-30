# How P4 turns cell certificates into divisor rates

This note explains the proof interfaces; compilation/acceptance status is in
`P4_CURRENT_CHECKPOINT.md`, not inferred from the existence of this note.

Let `n=L*N`, and let the accepted carry lower function be `B : R -> N`.
For the twelve-layer shape, L=69 and the base multiplicity is 17 (six copies
of offset zero and one copy of each offset 1 through 11).

## 1. Strictly interior windows

For a certified open cell `(a,b)` and a fixed integer period r, choose

    a < a' < b' < b,
    u=r+a', v=r+b'.

The prime window is deliberately half-open:

    N/v < p <= N/u.

It is exactly equivalent to `u <= N/p < v`. Hence the fractional part of
N/p lies strictly inside the original certified cell, even when a prime is
on an endpoint of the new window. There is no need to estimate the number
of primes satisfying rational endpoint equalities in this version.

Distinct original cells in the same period inherit separation from the
accepted cell table. Distinct periods are separated because all interior
endpoints lie strictly between r and r+1. Injectivity of the `(r,cell)` labels
therefore suffices to prove that a finite family has at most one active
window at any point. Individual weight lower bounds then imply the bound
on their sum; summing unrelated lower bounds without this step is invalid.

## 2. Why the selected primes belong to the actual divisor

The P3 divisor retains only primes satisfying

    p <= L*N < p*p.

The first inequality follows from `1 <= L*u` and `p <= N/u`.
For the second, the explicit sufficient threshold is `N > L*v^2`:

    p > N/v > L*v,
    L*N < L*p*v < p*p.

There are finitely many fixed windows, so their thresholds can be imposed
simultaneously before taking N to infinity. No uniform estimate over
infinitely many periods is used.

## 3. Exact logarithms and the prime number theorem

For the finite prime set above,

    sum log p = theta(N/u) - theta(N/v).

The audited unconditional PNT gives, for each fixed c>0,

    theta(N/c)/N -> 1/c.

Thus a fixed window with integer weight w contributes

    w*(1/u - 1/v)

to the logarithm divided by N. A fixed finite family has normalized rate

    gamma_F = (1/L) * sum_i w_i*(1/u_i - 1/v_i).

The normalization by L is essential: the construction is normalized by n,
not by its scale parameter N. Multiplying every window weight by an integer
u multiplies this rate by u.

Let

    Pi_N = product_{p<=L*N<(p*p)} p^(B(N/p)).

Extending each finite prime sum to the same large-prime index set and
interchanging the two finite sums shows

    sum_i w_i * sum_{p in window_i} log p <= log Pi_N.

P3-B proves Pi_N divides the actual common coefficient divisor D_N, for
every grouped realization. Both are positive. Consequently, for every
eta>0 and all sufficiently large N,

    exp((gamma_F-eta)*L*N) <= Pi_N <= D_N.

The final instantiated application uses the concrete 17-interval family,
not an unproved assertion that a grouped realization exists.

## 4. A small exact calibration

The table's cell `(1/69,1/68)` has weight 6. The interior window

    a'=3/206, b'=3/205, r=0

satisfies all strict endpoint and size-cap conditions. Its rate is

    (6/69)*(206/3 - 205/3) = 2/69.

This proves a positive rate for the actual family. It is intentionally a
small end-to-end calibration. It is far too weak to recover the manuscript's
proposed numerical irrationality bounds. Those require much larger finite
cell/period selections and certified rational comparisons. The general P4
interface supports those selections; the sharp arithmetic evaluation is
still a separate task. Neither this calibration nor the clean PNT audit is
a proof of any final numerical bound for a power of pi.

## 5. The lcm uses psi

The denominator sequence is `intervalLcm n = lcm(1,...,n)`. Mathlib's exact
identity is

    log(intervalLcm n) = psi(n),

where psi includes all prime powers. The audited psi asymptotic yields
`log(intervalLcm n)/n -> 1`. Replacing psi by theta would omit prime powers
and would not prove this exact interface.

## 6. What P5 must still supply

The divisor rate handles only the arithmetic improvement to the auxiliary
polynomials. P5 still needs uniform coefficient height bounds, finite-product
estimates on the whole contour, contour opening, integrable tails and the
central exponential rate. All thresholds must be uniform in the finite row
indices. Final odd-power bounds additionally need an explicit scaled family,
a strictly positive comparison gap and checked numerical constants. Existing
P1 transfer theorems do not replace these construction estimates.
