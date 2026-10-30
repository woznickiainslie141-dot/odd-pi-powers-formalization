# A rational finite tail for the P6 divisor certificate

The algebraic theorem in `Analysis/PeriodGapTail.lean` passed bounded source
probe `p6-period-gap-tail-trial02.log`. Final P6 root integration and axiom
audits remain separate obligations. The per-cell numeric data are accepted
only after their own ordinary kernel checks; candidate JSON is not a proof.

Put d=b-a>0, t=r+a>0, and

    f(t) = d/[t(t+d)],
    R(t) = d/t - d^2/(2t^2) + d/[2t(t+d)].

Clearing positive denominators gives the exact identity

    f(t) - R(t) + R(t+1)
      = d*[t(t+1)+(2t^2+2t+1)d^2+(2t+1)d^3]
        /[2t^2(t+1)^2(t+d)(t+d+1)] >= 0.

This is an algebraic certificate: the numerator has nonnegative factors,
and every denominator factor is positive. Summing over the FINITE interval
T <= r < K proves R(T+a)-R(K+a) <= sum f(r+a). If
x=d/(T+a), y=d/(K+a), it follows that

    x - x^2/2 - y + [periodGap(T,a,b)-periodGap(K,a,b)]/2
      <= sum_{T<=r<K} periodGap(r,a,b).

Indeed the left side is the telescoping lower bound minus y^2/2. No infinite
series, log approximation, integral estimate or PNT limit exchange is used.
PNT is applied afterwards to a fixed finite family of certified prime windows.
The large K=1000000 is kept symbolic in the analytic and window-family proofs.

For checking each tail floor cheaply, write a=A/C, b=B/D, Delta=BC-AD,
u=TC+A, v=KC+A, w=TD+B, z=KD+B. Then the weighted tail has denominator

    69*2*D^2*u^2*v*w*z

and integer numerator

    value * [2*Delta*D*u*v*w*z - Delta^2*v*w*z
             - 2*Delta*D*u^2*w*z
             + Delta*D^2*u*v*z - Delta*D^2*u^2*w].

`PeriodTailFloor.lean` proves this fraction identity and denominator
positivity from the cell endpoint hypotheses. Each proposed p/10^14 is
checked by an integer cross multiplication, before any summation. The
list checker accumulates only integer floor numerators, avoiding the
enormous common denominator of a direct sum of all exact rational terms.

Templates use the strict relative shrink

    a' = a + epsilon*(b-a), b' = b - epsilon*(b-a), epsilon=10^-24.

Validity supplies b>a, so the strict interior conditions follow uniformly;
no finite minimum-width estimate is needed. Selection requires a>=1/69,
value<=17. For every period, the gap loss is at most 2*69^2*epsilon.
With at most1180 cells and K periods the normalized weighted loss is at most

    2*69^2*epsilon*K*17*1180/69.

All of these inequalities are finite. For the actual selected cells,
generated exact candidates use T=32,K=1000000. Their intended combined floor
is 4.1305451873037 before shrinking; this decimal is an exact rational label,
not an assumed transcendental value. The sufficient base target is
4543599/1100000, giving the s=11 rate4543599/100000. The final sum comparison,
the actual divisor theorem, and fixed numerical transfer must all compile
and pass their exact transitive axiom audit before this becomes a P6 result.
