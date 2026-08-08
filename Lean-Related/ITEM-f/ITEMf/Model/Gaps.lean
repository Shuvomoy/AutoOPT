import ITEMf.Model.Transformed

/-!
# Shifted interpolation gaps and the ITEM-f three-point identity
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace SmoothConvexModel

/-- The generic interpolation-gap three-point identity at a stationary
reference point. -/
theorem interpolationGap_threePoint_of_grad_eq_zero
    (M : SmoothConvexModel E) {xStar : E}
    (hgradStar : M.grad xStar = 0) (x y : E) :
    M.interpolationGap x xStar -
        ⟪M.gradientStep x - xStar, M.grad y⟫_ℝ =
      M.interpolationGap x y - M.interpolationGap xStar y := by
  have hL : M.L ≠ 0 := ne_of_gt M.hL
  unfold interpolationGap gradientStep
  rw [hgradStar, norm_sub_sq_real, norm_sub_sq_real]
  simp only [sub_zero, zero_sub, norm_neg, norm_zero,
    inner_zero_left, inner_zero_right, inner_sub_left,
    real_inner_smul_left]
  rw [inner_sub_right, inner_sub_right,
    real_inner_comm (M.grad y) x,
    real_inner_comm (M.grad y) xStar]
  field_simp
  ring

end SmoothConvexModel

namespace StronglyConvexSmoothModel

/-- The explicit shifted gap is definitionally the interpolation gap of the
constructed shifted model. -/
theorem transformed_interpolationGap
    (M : StronglyConvexSmoothModel E) (xStar x y : E) :
    (M.transformedModel xStar).interpolationGap x y =
      M.shiftedGap xStar x y := by
  rfl

/-- The transformed reciprocal-smoothness step is the manuscript's original
gradient step scaled by `1 / (1-q)`. -/
theorem transformedStep_eq
    (M : StronglyConvexSmoothModel E) (xStar x : E) :
    (M.transformedModel xStar).gradientStep x - xStar =
      (1 / (1 - M.q)) • (M.gradientStep x - xStar) := by
  have hL0 : M.L ≠ 0 := ne_of_gt M.hL
  have hLm0 : M.L - M.μ ≠ 0 := ne_of_gt (sub_pos.mpr M.hμL)
  have hq :
      1 - M.q = (M.L - M.μ) / M.L := by
    rw [q]
    field_simp
  have hscale :
      1 / (1 - M.q) = M.L / (M.L - M.μ) := by
    rw [hq]
    field_simp
  have hcoef :
      (M.L - M.μ)⁻¹ * M.μ + 1 =
        M.L / (M.L - M.μ) := by
    field_simp
    ring
  have hgradCoef :
      (M.L / (M.L - M.μ)) * M.L⁻¹ =
        (M.L - M.μ)⁻¹ := by
    field_simp
  have hcoef' :
      1 + M.μ * (M.L - M.μ)⁻¹ =
        M.L / (M.L - M.μ) := by
    calc
      1 + M.μ * (M.L - M.μ)⁻¹ =
          (M.L - M.μ)⁻¹ * M.μ + 1 := by ring
      _ = M.L / (M.L - M.μ) := hcoef
  rw [hscale]
  change
    x - (M.L - M.μ)⁻¹ •
          (M.grad x - M.μ • (x - xStar)) - xStar =
      (M.L / (M.L - M.μ)) •
        (x - M.L⁻¹ • M.grad x - xStar)
  calc
    x - (M.L - M.μ)⁻¹ •
          (M.grad x - M.μ • (x - xStar)) - xStar =
        (1 + M.μ * (M.L - M.μ)⁻¹) • (x - xStar) -
          (M.L - M.μ)⁻¹ • M.grad x := by
            module
    _ = (M.L / (M.L - M.μ)) • (x - xStar) -
          (M.L - M.μ)⁻¹ • M.grad x := by rw [hcoef']
    _ = (M.L / (M.L - M.μ)) • (x - xStar) -
          ((M.L / (M.L - M.μ)) * M.L⁻¹) • M.grad x := by
            rw [hgradCoef]
    _ = (M.L / (M.L - M.μ)) •
          (x - M.L⁻¹ • M.grad x - xStar) := by
            module

end StronglyConvexSmoothModel

namespace Internal

/-- Public target I-A06: the exact three-point identity used by the
ITEM-f Lyapunov proof. -/
theorem threePointIdentity
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) (x y : E) :
    M.shiftedGap xStar x xStar -
        (1 / (1 - M.q)) *
          ⟪M.gradientStep x - xStar, M.shiftedGrad xStar y⟫_ℝ =
      M.shiftedGap xStar x y - M.shiftedGap xStar xStar y := by
  have hstar :
      (M.transformedModel xStar).grad xStar = 0 :=
    (M.transformedModel xStar).minimizer_grad_eq_zero
      (M.transformed_minimizer hxStar)
  have hthree :=
    (M.transformedModel xStar).interpolationGap_threePoint_of_grad_eq_zero
      hstar x y
  rw [M.transformedStep_eq xStar x, real_inner_smul_left] at hthree
  rw [M.transformed_interpolationGap xStar x xStar,
    M.transformed_interpolationGap xStar x y,
    M.transformed_interpolationGap xStar xStar y] at hthree
  exact hthree

end Internal

end ITEMf
