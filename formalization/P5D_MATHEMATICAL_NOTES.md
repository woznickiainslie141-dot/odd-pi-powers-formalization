# Explicit central majorants

Write n for the actual scale, M for the number of rows, m for a fixed
majorant degree, and h<=m for a row index. Assume n>0, Y>1/2 and
deg Q>=2(m+2). The typical choice is m=M-1. All finite interval endpoints
and all multiplicities are the actual construction's, not idealized limits.

## Constants and the complete line integral

Put B=(Y^2+1/4)^2/(Y^2-1/4), C=Y+1/2, and

    A_(m,Y) = (C+1)^m * max(1,B)^(m+2).

The accepted P5-A function g(t)=(|t|+C)^m/(1+t^2/B)^(m+2)
satisfies 0<=g(t)<=A_(m,Y)/(1+t^2). Consequently

    integral_R g(t) dt <= pi*A_(m,Y).

This constant is independent of n and h. It includes both infinite tails.
It can be large for fixed m,Y; its contribution to a logarithmic rate is
still log(A_(m,Y))/n, which tends to zero when m,Y are fixed. No limiting
rate theorem is inferred merely from this observation.

## Actual factorial kernel and contour normalization

Let F=product_a (length_a!) and

    K_h(theta,z) = F*z^h*exp(i*theta*(z+n))/Q(z),
    S = (M-1)!*lcm(1,...,n)^(M-1).

For either normalized line z=n*(t-1/2 +/- iY), the norm of the complete
integral is bounded by

    |F| * exp(|theta|*n*Y) * n^h/|Q(-n/2+i*n*Y)| * pi*A_(m,Y).

P5-C expresses the actual remainder as S*n/(2*pi*i) times lower minus
upper. The triangle inequality sums two copies of this bound. Thus 2*pi
cancels exactly and the resulting scalar is

    S*A_(m,Y)*n^(h+1)*exp(|theta|*n*Y)*|F|/|Q(-n/2+i*n*Y)|.

Since n is a positive integer, n>=1 and h<=m imply n^(h+1)<=n^(m+1).
At theta=pi/2, exp(i*theta)=i, and the left side is the actual row
sum_j A_(h,j)(i)*lambda^j. The same bound with n^(m+1) works for every
row. No row-dependent implicit constant occurs.

## The arithmetic quotient is the actual one

The accepted integer coefficient quotient gives a positive actual divisor D
and an actual Gaussian coefficient matrix B with D*B=A(i). Define

    U_h(z)=sum_j B_(h,j)*z^j.

Finite-sum distributivity proves D*U_h(z)=sum_j A_(h,j)(i)*z^j
for every complex z. Norms therefore divide the preceding bound by D.
This preserves the original determinant/nondegeneracy result; it does not
replace the divisor with a surrogate or introduce a smallness hypothesis.
All seventeen rows of the concrete family n=69*N satisfy these bounds
for every positive integer N and every Y>1/2.

## Exact finite logarithm

With u_r=r/n-1/2, the exact formula is

    log|Q(-n/2+i*n*Y)|
      = d*log n + (1/2)*sum_a sum_(r in interval_a) log(u_r^2+Y^2),

where d=sum_a(length_a+1), retaining every extra endpoint. Therefore

    centralLogRatio(Y)
      = sum_a log(length_a!) - d*log n
          - (1/2)*sum_a sum_r log(u_r^2+Y^2).

The logarithm of the positive central bound is exactly

    log S + log A_(m,Y) + (h+1)*log n
      + |theta|*n*Y + centralLogRatio(Y).

For the reduced row, subtract log D inside the exponential. This is an
exact finite-scale inequality. Establishing the limiting value of the
factorial/Riemann expression remains a separate obligation.

## Single-interval integral

For Y>0 an antiderivative of log(sqrt(u^2+Y^2)) is

    (u/2)*log(u^2+Y^2) - u + Y*arctan(u/Y).

For c>=0, evaluation at +/-c/2 yields

    integral = (c/2)*log(Y^2+c^2/4) - c + 2Y*arctan(c/(2Y)).

The associated single-interval function is

    F_c(Y)=(c/2)*log(Y^2+c^2/4)-c*log c+2Y*arctan(c/(2Y)).

Its first height derivative is 2*arctan(c/(2Y)); the derivative of that
explicit function is -c/(Y^2+c^2/4). Zero width is included, with
Real.log(0)=0 and F_0=0. These calculus identities do not establish any
discrete asymptotic, existence/uniqueness of an optimal height, or numerical
irrationality exponent by themselves.

## Remaining work

For the base family, n=69*N, six intervals have c=1 and the other eleven
have c_a=1-2*a/69, a=1,...,11. The sum of the integer interval lengths is
1041*N and the total denominator degree is 1041*N+17. Thus the exact finite
logarithm has seventeen extra log(n) endpoint terms. The intended next
per-interval result is

    (log(length!) - (length+1)*log n
       - sum_r log(sqrt((r/n-1/2)^2+Y^2)))/n -> -F_c(Y).

It needs both Stirling and a Riemann-sum theorem along the actual rational
grid, with fixed Y>1/2. The extra log(n)/n tends to zero; it must be proved
to do so, rather than dropped in the finite identity. Summing the seventeen
fixed terms would then identify centralLogRatio(Y)/n. Combining with the
already accepted log-lcm rate, and the new exact logarithmic majorant, gives
the intended unreduced rate 16+(pi/2)*Y-sum_a F_(c_a)(Y). Divisor improvement
then subtracts gamma. These displayed limiting conclusions are a roadmap,
not accepted P5-D theorems.

Uniform coefficient heights; Stirling and Riemann-sum limits for the actual
scaled intervals; sharp arithmetic gamma; explicit scaled families and
odd-power parameters; and certified final numerical comparisons remain
open. P5-D is a finite quantitative bridge to those obligations.
