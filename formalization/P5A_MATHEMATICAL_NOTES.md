# Whole-line horizontal domination for the actual denominator

This explains the P5-A proof interfaces. Acceptance is recorded separately in
P5A_REVIEW_2026-10-29.md and the final machine-readable log; source existence
alone does not establish acceptance.

## The objects are the actual construction

For `P : ActualIntervals M`, let

    Q(z) = product_a product_{r in [left_a,n-left_a]} (z+r),
    d = totalMultiplicity = degree Q,
    z(t,Y) = n*(t-1/2+iY),
    u_r = r/n-1/2.

For n>0 the exact polynomial evaluation identity is

    Q(z(t,Y)) = n^d * product_a product_r (t+u_r+iY).

Every endpoint and every repeated interval contributes. Both the degree and
normalization identities are proved in `ActualHorizontalGeometry.lean`.
The horizontal denominator never vanishes when Y is nonzero: each factor
has nonzero imaginary part nY. No nonvanishing assumption is introduced as
an unexplained field of a structure.

## Reflection without a parity split

For Y>1/2 put

    B = (Y^2+1/4)^2/(Y^2-1/4) > 0,
    b(t) = 1+t^2/B,
    f(u,t) = |t+u+iY|^2.

The accepted pair inequality implies

    (b(t)*f(u,0))^2 <= f(u,t)*f(-u,t),     |u|<=1/2.

Inside each actual interval, r maps bijectively to n-r and u_(n-r)=-u_r.
Consequently the finite product of f(-u_r,t) equals the product of f(u_r,t).
Multiply the displayed pair inequality over every pole occurrence and take
the nonnegative square root. This proves

    b(t)^d * |Q(z(0,Y))|^2 <= |Q(z(t,Y))|^2.

Equivalently, the norm ratio is at least b(t)^(d/2). The Lean statement keeps
squared norms, so the exact degree exponent is a natural number. This avoids
fractional-power conventions while retaining the full mathematical statement.

Reflection fixed points are included in the same product. If n is even and
r=n/2, the argument uses that single central factor through the squared
product identity; it is neither discarded nor counted twice in d. Repeated
intervals remain separate outer factors, so their multiplicities are exact.

Complex conjugation at the level of norm squares gives the same bound for
the lower line. For any integer j with 2j<=d, the practical consequence is

    b(t)^j * |Q(z(0,Y))| <= |Q(z(t,Y))|.

## A majorant independent of scale and row

Fix m and Y>1/2, and assume d>=2(m+2). Let C=Y+1/2. The triangle inequality
and h<=m give

    |z(t,Y)|^h <= n^h * (|t|+C)^m.

The use of h<=m is valid because |t|+C>=1. Define

    g(t) = (|t|+C)^m/(1+t^2/B)^(m+2).

For the actual rational kernel K_h(t)=z(t,Y)^h/Q(z(t,Y)), the proof gives

    |K_h(t)| <= n^h/|Q(z(0,Y))| * g(t).

For the normalized complex kernel

    Khat_h(t) = Q(z(0,Y))/n^h * K_h(t),

we therefore have |Khat_h(t)|<=g(t). The very same g works for both horizontal
lines and all h<=m. It depends only on Y and m, not on n, the row, or any
rational approximant p/q. The normalized kernel is itself proved integrable,
not just formally bounded by a conjectured integrable expression.

## Why the entire majorant is integrable

The proof does not replace a pointwise tail assertion by an integrability
claim. It establishes the global bound

    0 <= g(t) <= A/(1+t^2),
    A = (C+1)^m * max(1,B)^(m+2).

Indeed let v=1+t^2 and H=max(1,B). Then |t|<=v, v>=1, and

    |t|+C <= (C+1)*v,
    v <= H*(1+t^2/B).

Raise these nonnegative inequalities to integer powers. Multiplication by v
leaves enough denominator power to obtain the displayed Cauchy bound on
all of R, including the compact central interval. Mathlib's proved
integrability of (1+t^2)^(-1), together with continuity and domination,
therefore establishes integrability of g. No external quadrature is used.
The Bochner integral bound is also connected to the actual kernel:

    |integral_R K_h(t) dt| <= n^h/|Q(z(0,Y))| * integral_R g(t) dt.

## A fully instantiated family

An interval with left endpoint zero contributes n+1 factors, so d>=n+1.
The actual twelve-layer family has 17 intervals, including six such outer
intervals, n=69N and rows h=0,...,16. Thus every N>=1 already satisfies

    d >= 69N+1 >= 2*(16+2).

`twelveLayer_horizontal_uniform_majorant` supplies one integrable g for all
positive N, all 17 rows, and both horizontal lines. This instantiation uses
the actual family constructed and accepted in P4, not a hypothetical family.

## Remaining analytic obligations

P5-A proves a rational-kernel domination result. It does not identify the
auxiliary remainder with a horizontal integral. Later work must prove the
contour/residue representation, vanishing vertical sides for fixed n and
the branch/exponential factors, then obtain coefficient heights and the
central exponential rate via Stirling and Riemann sums. The Jacobian n and
the exponential factor on the horizontal line must be included there.

No sharp gamma or final irrationality exponent follows from this stage.
The deliberately coarse majorant changes a scale-independent prefactor,
not a claimed optimized central rate. P4's 2/69 remains only a small
arithmetic calibration until sharper finite-window certificates are proved.
