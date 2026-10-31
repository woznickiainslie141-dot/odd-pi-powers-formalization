# All integer powers: manuscript scope, prior bounds and a uniform target

31 October 2026. This is a mathematical review and a proposed formalization
target. It does not extend the accepted Lean scope by itself. L99 remains
accepted; no new compiler run or general-power acceptance is claimed here.

## 1. What the existing manuscript says

`output/pdf/odd_pi_powers_notes/sections/01_overview.tex` states the parameter
bound m(D+G)/(D-(k-1)G), initially for odd k>=3. Its following paragraph says
the proof also works for every integer k>=2. The accepted Lean theorem
`OddPiPowers.irrationality_transfer` indeed assumes only2<=k, not oddness.

Section06, Proposition6.1 (label `prop:allodd`), gives a root-free recipe.
For the twelve-layer base weights(6,1,...,1), let V=17, S=347/23,
Theta=pi/2, gamma_* be the base divisor rate, and

    g = V + S log2 - gamma_*,
    A = sum_j v_j c_j log(c_j),
    d = S log(S/Theta) - A - V + gamma_*.

Choose s=max(1,ceil(exp(((k-1)g-d)/S+1))), m=Vs-1, and put

    D_lower = s(S log s+d)+1-Theta^2/(12sS),
    G = sg-1.

The proposition proves a positive gap D_lower-(k-1)G and hence

    mu(pi^k) <= (Vs-1)(D_lower+G)/(D_lower-(k-1)G).

Its statement quantifies over every integer k>=3. Thus this is already a
definite parameter recipe, rather than just an assertion that a search will
eventually succeed. The manuscript emphasizes odd powers for motivation.
It estimates growth O(k*rho^k), rho about4.69344, for this particular recipe.

The manuscript's numerical k=5,7,9 bounds are42461,1272103,35398937. Their
decimal certifications are Arb computations under the written arguments.
They are not yet accepted fixed Lean applications. The accepted fixed L99
application remains k=3, with exponent12970477737/11706979<1107.93.

## 2. An explicit prior bound already exists for every k

Source verified in the original paper:

Yu. Nesterenko and M. Waldschmidt, *On the approximation of the values of
exponential function and logarithm by algebraic numbers*, Mat. Zapiski2
(1996),23-42; English preprint arXiv:math/0002047, submitted7 February2000.
Theorem2(1), PDF page2:

https://arxiv.org/pdf/math/0002047

For real algebraic xi of degree d and coefficient length at most L>=3,

    |pi-xi| >= exp(-1200000*d*(log L+d log d)*(1+log d)).

This implies, by the following elementary specialization, the prior bound

    mu(pi^k) <= A(k) := 1200000*k*(1+log k)       (k>=1).

The displayed conclusion is our deduction from their theorem, not a quoted
statement that they explicitly tabulate for each power.

Take p/q close enough that |pi^k-p/q|<1, q>=1, and p/q>0. Set
theta=(p/q)^(1/k), of degree d<=k. Its primitive integral minimal polynomial
divides qX^k-p after removing content, so its leading coefficient is at most
q. Every conjugate is a root of this binomial and has absolute value theta.
Since theta<=pi+1, its coefficient length is at most

    q(1+theta)^d <= q(pi+2)^k < 6^k q.

This argument also handles reducible binomials; it does not assume d=k or
that the minimal polynomial has length at most p+q. Applying Theorem2(1),
using monotonicity in d, gives

    |pi-theta| >= (6k)^(-k*A(k))*q^(-A(k)).

Factorization gives |pi^k-p/q| >= pi^(k-1)|pi-theta|. Outside the chosen
neighborhood the error is at least1. Consequently the completely explicit
lower bound

    |pi^k-p/q| >= (6k)^(-k*A(k))*q^(-A(k))

holds for all integers p, q>=1. This establishes the claimed exponent bound.
No unknown large-degree threshold is used.

For comparison:

| k | A(k), approximately | Present manuscript bound |
|---|---:|---:|
|3|7,555,004.239205|1107.93 (accepted L99 Lean instance)|
|5|15,656,627.474605|42,461 (manuscript + Arb)|
|7|24,745,645.252065|1,272,103 (manuscript + Arb)|
|9|34,530,025.435231|35,398,937 (manuscript + Arb)|

In particular the older general theorem already beats the manuscript's
twelve-layer k=9 number. This does not compare all available literature and
does not establish any best-known or priority claim. It decisively rules
out claiming that no earlier explicit numerical bound could be deduced.
The classical O(k log k) upper bound also eventually beats this manuscript's
O(k rho^k) family. The manuscript correctly disclaims a first finiteness
theorem, but its introduction should additionally cite this explicit prior
bound when discussing novelty or usefulness of the numerical table.

For an even simpler deduction avoiding algebraic minimal polynomials,
Theorem2(2), applied directly to P=qX^k-p, gives

    mu(pi^k) <= 1+2000000*k*(1+log k).

## 3. A simple uniform target from the already accepted L99 shape

The same root-free argument works with L99 base weights v0=16,
vj=1 (1<=j<=27), cj=(99-2j)/99, and the *proved rational lower rate*

    V=43, S=389/11, gamma0=2761813/200000.

Define g,A,d as above with these constants and gamma0. This uses only the
accepted finite divisor lower bound, rather than the exact infinite arc rate.
All positive scales s are supported by the accepted actual scaled family,
grouping and finite-window rate interface.

A deliberately conservative, fully specified theorem target is

    forall integer k>=3, mu(pi^k) <= 301*8^k.

It has the following short paper-level derivation. From
2/3<=log2<=3/4,35<S<36 and13<gamma0<43, one has1<g<60. Also cj<=1 gives
A<=0. Since S/Theta>e, log(S/Theta)>1, and
S-43+gamma0>0, one has d>0. Choose the exact integer s=8^k. Then

    S log s >= 70k,
    0 < Theta^2/(12sS) < 1,
    Delta := D_lower-(k-1)G
           = s(S log s+d-(k-1)g)+k-Theta^2/(12sS)
           > 10ks,
    0 < G=sg-1 < 60s.

The existing transfer yields

    E = (43s-1)(1+kG/Delta) < 43s*(1+6) = 301*8^k.

The trial height is Y=sS/Theta>1/2, so the actual-family analytic interface
applies. This target avoids defining the precise optimal scale or computing
an exponentially large determinant/table for each k. It is an intentionally
loose formalization target, not a new literature record and not yet an
accepted Lean theorem.

The remaining Lean work is the generic trial-height lower estimate, its
coarse constant bounds, the natural-power/log identities for s=8^k, and
assembly with the already accepted transfer for arbitrary k>=3. The fixed
3004-cell certificate and the universal scaled construction can be reused.
Sharper k-specific applications and a better exponential base can follow
separately; they are not needed to close the all-k quantifier.

## 4. Scope of explicitness

The manuscript makes the exponent E(k) explicit. Section07 explicitly does
not give numerical q0(epsilon) or c_epsilon in its approximation inequality;
these require an additional effective prime-counting/error analysis. Do not
describe the manuscript as already providing all such constants. The
classical deduction in section2 above has its own explicitly displayed
prefactor, independent of the manuscript's asymptotic PNT construction.
