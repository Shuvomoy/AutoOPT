import LemniAcc.FiniteInterpolation
import LemniAcc.Spec.Discrete

/-!
# Smooth-convex gaps used by the discrete Lyapunov proof

This module names the pairwise interpolation residual and proves the
three-point identity used to regroup the terminal and decrement expansions.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

namespace Discrete

/-- Every actual smooth-convex interpolation gap is nonnegative. -/
theorem gap_nonneg
    (M : SmoothConvexModel E) (x y : E) :
    0 ≤ gap M x y :=
  M.interpolationGap_nonneg x y

@[simp] theorem gap_self
    (M : SmoothConvexModel E) (x : E) :
    gap M x x = 0 := by
  simp [gap, SmoothConvexModel.interpolationGap]

/-- A minimizer is fixed by the reciprocal-smoothness gradient step. -/
theorem corrected_minimizer
    (M : SmoothConvexModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) :
    corrected M xStar = xStar := by
  rw [corrected, SmoothConvexModel.gradientStep,
    M.minimizer_grad_eq_zero hxStar, smul_zero, sub_zero]

/-- The interpolation-gap three-point identity from the manuscript. -/
theorem gap_three_point
    (M : SmoothConvexModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) (x y : E) :
    gap M x xStar - ⟪corrected M x - xStar, M.grad y⟫_ℝ =
      gap M x y - gap M xStar y := by
  have hL : (M.L : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt M.hL
  have hgradStar : M.grad xStar = 0 :=
    M.minimizer_grad_eq_zero hxStar
  unfold gap corrected SmoothConvexModel.interpolationGap
    SmoothConvexModel.gradientStep
  rw [hgradStar, norm_sub_sq_real, norm_sub_sq_real]
  simp only [sub_zero, zero_sub, norm_neg, norm_zero,
    inner_zero_left, inner_zero_right, inner_sub_left,
    real_inner_smul_left]
  rw [inner_sub_right, inner_sub_right,
    real_inner_comm (M.grad y) x,
    real_inner_comm (M.grad y) xStar]
  field_simp
  ring

end Discrete

end LemniAcc
