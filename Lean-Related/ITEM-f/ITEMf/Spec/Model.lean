import ITEMf.Spec.Basic

/-!
# First-order models for analytic ITEM-f

The manuscript uses differentiable smooth convex and smooth strongly convex
objectives.  For the finite proof, their exact first-order lower and upper
quadratic inequalities are the smallest useful interface.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A convex objective with an `L`-smooth first-order model. -/
structure SmoothConvexModel (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  f : E → ℝ
  grad : E → E
  L : ℝ
  hL : 0 < L
  lower : ∀ x y : E, f x + ⟪grad x, y - x⟫_ℝ ≤ f y
  upper : ∀ x y : E,
    f y ≤ f x + ⟪grad x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2

namespace SmoothConvexModel

/-- A global minimizer of a smooth-convex first-order model. -/
def IsMinimizer (M : SmoothConvexModel E) (xStar : E) : Prop :=
  ∀ x : E, M.f xStar ≤ M.f x

/-- One reciprocal-smoothness gradient step. -/
noncomputable def gradientStep (M : SmoothConvexModel E) (x : E) : E :=
  x - M.L⁻¹ • M.grad x

/-- The pairwise smooth-convex interpolation residual. -/
noncomputable def interpolationGap
    (M : SmoothConvexModel E) (x y : E) : ℝ :=
  M.f x - M.f y - ⟪M.grad y, x - y⟫_ℝ -
    (1 / (2 * M.L)) * ‖M.grad x - M.grad y‖ ^ 2

end SmoothConvexModel

/-- A `μ`-strongly convex objective with an `L`-smooth first-order model. -/
structure StronglyConvexSmoothModel (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  f : E → ℝ
  grad : E → E
  L : ℝ
  μ : ℝ
  hμ : 0 < μ
  hμL : μ < L
  lower : ∀ x y : E,
    f x + ⟪grad x, y - x⟫_ℝ + (μ / 2) * ‖y - x‖ ^ 2 ≤ f y
  upper : ∀ x y : E,
    f y ≤ f x + ⟪grad x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2

namespace StronglyConvexSmoothModel

/-- A global minimizer of a smooth strongly convex model. -/
def IsMinimizer (M : StronglyConvexSmoothModel E) (xStar : E) : Prop :=
  ∀ x : E, M.f xStar ≤ M.f x

/-- The condition ratio `q = μ / L`. -/
noncomputable def q (M : StronglyConvexSmoothModel E) : ℝ :=
  M.μ / M.L

/-- One reciprocal-`L` gradient step for the original objective. -/
noncomputable def gradientStep
    (M : StronglyConvexSmoothModel E) (x : E) : E :=
  x - M.L⁻¹ • M.grad x

/-- The shifted objective used in the ITEM-f Lyapunov proof. -/
noncomputable def shiftedF
    (M : StronglyConvexSmoothModel E) (xStar x : E) : ℝ :=
  M.f x - M.f xStar - (M.μ / 2) * ‖x - xStar‖ ^ 2

/-- The gradient of the shifted objective. -/
noncomputable def shiftedGrad
    (M : StronglyConvexSmoothModel E) (xStar x : E) : E :=
  M.grad x - M.μ • (x - xStar)

/-- The interpolation gap of the shifted objective, written directly in
manuscript variables so theorem statements do not depend on a proof-bearing
construction of the shifted model. -/
noncomputable def shiftedGap
    (M : StronglyConvexSmoothModel E) (xStar x y : E) : ℝ :=
  M.shiftedF xStar x - M.shiftedF xStar y -
    ⟪M.shiftedGrad xStar y, x - y⟫_ℝ -
    (1 / (2 * (M.L - M.μ))) *
      ‖M.shiftedGrad xStar x - M.shiftedGrad xStar y‖ ^ 2

end StronglyConvexSmoothModel

end ITEMf
