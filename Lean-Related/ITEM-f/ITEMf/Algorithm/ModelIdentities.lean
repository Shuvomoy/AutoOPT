import ITEMf.Algorithm.Iterates
import ITEMf.Model.Gaps

/-!
# Scalar and gradient-step identities for ITEM-f
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace StronglyConvexSmoothModel

theorem q_pos (M : StronglyConvexSmoothModel E) : 0 < M.q :=
  (M.q_unit).1

theorem q_lt_one (M : StronglyConvexSmoothModel E) : M.q < 1 :=
  (M.q_unit).2

theorem q_ne_zero (M : StronglyConvexSmoothModel E) : M.q ≠ 0 :=
  ne_of_gt M.q_pos

theorem one_sub_q_pos (M : StronglyConvexSmoothModel E) :
    0 < 1 - M.q :=
  sub_pos.mpr M.q_lt_one

theorem one_sub_q_ne_zero (M : StronglyConvexSmoothModel E) :
    1 - M.q ≠ 0 :=
  ne_of_gt M.one_sub_q_pos

theorem q_mul_L (M : StronglyConvexSmoothModel E) :
    M.q * M.L = M.μ := by
  have hL0 : M.L ≠ 0 := ne_of_gt M.hL
  rw [q]
  field_simp

theorem one_sub_q_mul_L (M : StronglyConvexSmoothModel E) :
    (1 - M.q) * M.L = M.L - M.μ := by
  rw [sub_mul, one_mul, M.q_mul_L]

/-- The manuscript identity
`x⁺-x⋆ = (1-q)(x-x⋆) - L⁻¹ g̃(x)`. -/
theorem gradientStep_sub_eq
    (M : StronglyConvexSmoothModel E) (xStar x : E) :
    M.gradientStep x - xStar =
      (1 - M.q) • (x - xStar) -
        M.L⁻¹ • M.shiftedGrad xStar x := by
  have hL0 : M.L ≠ 0 := ne_of_gt M.hL
  have hqL := M.q_mul_L
  have hcoef : 1 - M.q + M.L⁻¹ * M.μ = 1 := by
    rw [← hqL]
    field_simp
    ring
  simp only [gradientStep, shiftedGrad]
  calc
    x - M.L⁻¹ • M.grad x - xStar =
        (x - xStar) - M.L⁻¹ • M.grad x := by module
    _ = (1 - M.q + M.L⁻¹ * M.μ) • (x - xStar) -
        M.L⁻¹ • M.grad x := by rw [hcoef]; simp
    _ = (1 - M.q) • (x - xStar) -
        M.L⁻¹ • (M.grad x - M.μ • (x - xStar)) := by module

/-- Rearranged shifted-gradient identity used in the initial norm
calculation. -/
theorem shiftedGrad_eq
    (M : StronglyConvexSmoothModel E) (xStar x : E) :
    M.shiftedGrad xStar x =
      (1 - M.q) • M.grad x +
        (-M.μ) • (M.gradientStep x - xStar) := by
  have hL0 : M.L ≠ 0 := ne_of_gt M.hL
  have hqL := M.q_mul_L
  have hcoef : 1 - M.q + M.μ * M.L⁻¹ = 1 := by
    rw [← hqL]
    field_simp
    ring
  simp only [gradientStep, shiftedGrad]
  calc
    M.grad x - M.μ • (x - xStar) =
        (1 - M.q + M.μ * M.L⁻¹) • M.grad x -
          M.μ • (x - xStar) := by rw [hcoef]; simp
    _ = (1 - M.q) • M.grad x +
        (-M.μ) • (x - M.L⁻¹ • M.grad x - xStar) := by module

end StronglyConvexSmoothModel

end ITEMf
