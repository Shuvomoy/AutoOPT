# Composite primitives

Use this reference when an instance involves a finite or signed sum of functions, a composite or difference-of-convex stationary point, or an exact Euclidean proximal map for a proper closed convex function class already covered by `interpolation-conditions.md`.

## Finite sums

Represent a composite objective as
\[
F(x)=\sum_{\ell=1}^m a_\ell f_\ell(x),
\]
where each component \(f_\ell\) has its own interpolation or oracle constraints. The weights \(a_\ell\) may be positive or negative for a signed composition such as \(F=f_1-f_2\). The point sample \(x_i\) is shared across components, but component gradients and values are separate:
\[
(x_i,g_{\ell,i},f_{\ell,i})\quad \text{for component } f_\ell.
\]
The composite value at \(x_i\) is the scalar expression
\[
F_i=\sum_{\ell=1}^m a_\ell f_{\ell,i}.
\]
Do not impose interpolation constraints directly on \(F\) unless a valid class condition for \(F\) is supplied. Instead, impose the appropriate constraints separately on each component. In particular, do not call a signed composite convex or smooth-convex merely because its components are smooth-convex.

## Composite stationarity

For a composite minimizer \(x_\star\), stationarity means
\[
0\in \sum_{\ell=1}^m a_\ell \partial f_\ell(x_\star).
\]
In the finite model, introduce component samples \((x_\star,g_{\ell,\star},f_{\ell,\star})\) and impose
\[
\sum_{\ell=1}^m a_\ell g_{\ell,\star}=0.
\]
For unit-weight sums this is \(\sum_{\ell=1}^m g_{\ell,\star}=0\). The composite optimum value is
\[
F_\star=\sum_{\ell=1}^m a_\ell f_{\ell,\star}.
\]

For a difference-of-convex objective \(F=f_1-f_2\) with differentiable components, a stationary point \(x_\star\) satisfies
\[
\nabla f_1(x_\star)=\nabla f_2(x_\star).
\]
Represent this by either one shared vector \(g_\star\) used as both component gradients at \(x_\star\), or by two gradient vectors with the equality \(g_{1,\star}-g_{2,\star}=0\). The value is
\[
F_\star=f_{1,\star}-f_{2,\star}.
\]

When generating code, it is often simplest to create independent gradient coefficient vectors for all but one component at \(x_\star\), then define the remaining component gradient by the stationarity equation. This avoids adding redundant vector-balance constraints to the Gramian basis.

## Exact proximal maps

For a proper closed convex function \(f\) and \(\gamma>0\),
\[
x=\mathbf{prox}_{\gamma f}(u)
\quad\Longleftrightarrow\quad
x=u-\gamma g_f(x),\qquad g_f(x)\in\partial f(x).
\]
The generated finite model should:

1. create a component sample \((x,g_f(x),f(x))\);
2. express \(x\) as the affine combination \(u-\gamma g_f(x)\) in the shared Gramian basis;
3. include the usual interpolation constraints for \(f\) over all of its component samples.

If \(u\) is itself an affine expression involving previously sampled points or gradients, expand it directly. For example, for a proximal-gradient step
\[
u=y-\frac{1}{L}\nabla h(y),\qquad x=\mathbf{prox}_{\gamma f}(u),
\]
encode
\[
x=y-\frac{1}{L}g_h(y)-\gamma g_f(x).
\]

For an indicator function \(\delta_C\), the same rule gives the projection relation
\[
x=\mathbf{proj}_C(u)
\quad\Longleftrightarrow\quad
u-x\in \gamma N_C(x).
\]
Use the indicator-function row in `interpolation-conditions.md` for the normal-cone and domain constraints.

## OptISTA-style double-function composite/proximal FSFOM pattern

Use this generic OptISTA-style pattern for composite problems
\[
\min_x\ F(x)=f(x)+h(x),
\]
where \(f\) is smooth convex and \(h\) is proper closed convex. Keep the two
function blocks separate:

- samples for \(f\): \((w_i,g_i^f,f_i)\) on the points where gradients of \(f\)
  are queried, usually \(x_0,\ldots,x_N\) and \(x_\star\);
- samples for \(h\): \((w_i,g_i^h,h_i)\) on the prox output points, usually
  \(y_1,\ldots,y_N\) and \(x_\star\);
- composite values assembled only as \(F_i=f_i+h_i\) when both component values
  are defined at the relevant point.

If the performance measure or the initial condition references a component
value at a point, for example \(F(y_N)=f(y_N)+h(y_N)\) at a prox output,
sample that component there as well, introducing a free gradient or subgradient
vector for it if the method never queries one, and include those extra samples
when counting the Gramian basis size.

A double-function fixed-step method may define both prox-generated points and
output points by affine combinations of the initial point, smooth gradients, and
proximal subgradients:
\[
y_{i+1}=x_0-\sum_{j=0}^i a_{i+1,j}g_j^f-\sum_{j=0}^i b_{i+1,j}g_{j+1}^h,
\]
\[
x_{i+1}=x_0-\sum_{j=0}^i c_{i+1,j}g_j^f-\sum_{j=0}^i d_{i+1,j}g_{j+1}^h.
\]
When \(y_{i+1}\) is produced by a prox call, introduce the pre-prox point
\[
\tilde y_{i+1}=x_0-\sum_{j=0}^i a_{i+1,j}g_j^f-\sum_{j=0}^{i-1} b_{i+1,j}g_{j+1}^h
\]
and encode the exact graph relation
\[
y_{i+1}=\mathbf{prox}_{\gamma_{i+1}h}(\tilde y_{i+1})
\quad\Longleftrightarrow\quad
y_{i+1}=\tilde y_{i+1}-\gamma_{i+1}g_{i+1}^h,\qquad
g_{i+1}^h\in\partial h(y_{i+1}).
\]
For the common normalization \(\gamma_{i+1}=b_{i+1,i}\), require
\(\gamma_{i+1}>0\); if the user supplies a zero or sign-free coefficient, ask
for the intended graph relation before deriving.

At a composite minimizer, impose
\[
g_\star^f+g_\star^h=0.
\]
Use one shared Gramian basis for \(x_0\), all \(g_i^f\), and all \(g_i^h\). The
large-scale assumption must cover that basis dimension; for the usual two-block
\(N\)-step pattern it is of order \(2N+4\), but the derivation should compute
the exact basis size from the declared samples, including any samples added
because the performance measure or initial condition references component
values at output or prox-output points.

### Difference-of-convex value and residual assembly

For a differentiable signed composite \(F=f_1-f_2\), assemble gaps and residuals from component samples:
\[
F_i-F_\star=(f_{1,i}-f_{2,i})-(f_{1,\star}-f_{2,\star}),
\qquad
r_i=\nabla f_1(x_i)-\nabla f_2(x_i).
\]
An initial normalization \(F_0-F_\star\le1\) becomes
\[
1-\bigl(f_{1,0}-f_{2,0}-f_{1,\star}+f_{2,\star}\bigr)\ge0.
\]
A supplied lower-bound constraint of the form
\[
F_i-F_\star-c\|r_i\|^2\ge0
\]
becomes the scalar-plus-Gram inequality
\[
f_{1,i}-f_{2,i}-f_{1,\star}+f_{2,\star}-c\|r_i\|^2\ge0.
\]
For a performance measure
\[
\min_{i\in I}\|r_i\|^2,
\]
use an epigraph scalar \(\tau\) and constraints
\[
\|r_i\|^2-\tau\ge0\qquad(i\in I),
\]
then maximize \(\tau\) in the primal SDP. The dual SDP uses nonnegative multipliers \(\eta_i\) for these performance inequalities, and stationarity in the \(\tau\) coefficient gives \(\sum_{i\in I}\eta_i=1\).

## Primal and dual coefficient assembly

For each component \(f_\ell\), build one interpolation block with its own scalar variables \(f_{\ell,i}\), gradient vectors \(g_{\ell,i}\), and nonnegative dual multipliers. All blocks share the same Gramian matrix because their point and gradient vectors live in the same ambient Hilbert space.

Composite expressions enter initial conditions and performance measures only through linear combinations of component values and Gramian inner products. For example,
\[
F_N-F_\star=\sum_{\ell=1}^m a_\ell (f_{\ell,N}-f_{\ell,\star}).
\]
In the dual SDP, this means each component interpolation block contributes its own multiplier-weighted coefficient matrix and scalar function-value coefficients; stationarity and proximal-map equations are already encoded through vector coefficient definitions.

## Current limits

This reference covers exact Euclidean proximal-map graph relations for proper closed convex functions and signed finite-composite value/residual assembly. It does not cover inexact proximal maps, stochastic finite-sum expectations, mirror-geometry primitives, broad oracle catalogs, or unrelated LMI-valued interpolation classes. Do not infer other unsupported rules from the exact proximal-map relations above.
