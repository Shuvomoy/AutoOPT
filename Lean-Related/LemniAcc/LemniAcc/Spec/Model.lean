import LemniAcc.Spec.Basic

/-!
# Proof-free smooth-convex model declarations
-/

open scoped InnerProductSpace
open Set
open InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

/-- A differentiable convex function with a positive Lipschitz-gradient
constant. -/
structure SmoothConvexModel
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  f : E → ℝ
  grad : E → E
  L : NNReal
  hL : 0 < L
  convex : ConvexOn ℝ Set.univ f
  hasGradient : ∀ x : E, HasGradientAt f (grad x) x
  gradLipschitz : LipschitzWith L grad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace SmoothConvexModel

/-- A point is a global minimizer of the model objective. -/
def IsMinimizer (M : SmoothConvexModel E) (xStar : E) : Prop :=
  ∀ x : E, M.f xStar ≤ M.f x

/-- The smooth-convex interpolation residual with orientation `(x,y)`. -/
noncomputable def interpolationGap
    (M : SmoothConvexModel E) (x y : E) : ℝ :=
  M.f x - M.f y - ⟪M.grad y, x - y⟫_ℝ -
    (1 / (2 * (M.L : ℝ))) * ‖M.grad x - M.grad y‖ ^ 2

/-- The Bregman divergence with gradient evaluated at the second point. -/
noncomputable def bregman
    (M : SmoothConvexModel E) (x y : E) : ℝ :=
  M.f x - M.f y - ⟪x - y, M.grad y⟫_ℝ

/-- One gradient step with reciprocal smoothness stepsize. -/
noncomputable def gradientStep
    (M : SmoothConvexModel E) (x : E) : E :=
  x - ((M.L : ℝ)⁻¹) • M.grad x

end SmoothConvexModel

end LemniAcc
