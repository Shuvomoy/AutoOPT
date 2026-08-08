import ITEMf.Model.FiniteInterpolation

/-!
# Quadratic shift of a smooth strongly convex objective

Subtracting the strong-convexity quadratic produces the convex
`(L - μ)`-smooth model used throughout the ITEM-f Lyapunov proof.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace SmoothConvexModel

/-- A global minimizer of the first-order model has zero model gradient. -/
theorem minimizer_grad_eq_zero
    (M : SmoothConvexModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) :
    M.grad xStar = 0 := by
  let g : E := M.grad xStar
  let y : E := xStar - M.L⁻¹ • g
  have hmin := hxStar y
  have hup := M.upper xStar y
  have hL0 : M.L ≠ 0 := ne_of_gt M.hL
  have hy : y - xStar = (-M.L⁻¹) • g := by
    dsimp [y]
    module
  have habs : |M.L⁻¹| = M.L⁻¹ :=
    abs_of_pos (inv_pos.mpr M.hL)
  have hself : ⟪g, g⟫_ℝ = ‖g‖ ^ 2 :=
    real_inner_self_eq_norm_sq g
  rw [hy, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_neg, habs, hself] at hup
  have hcoef :
      M.L / 2 * (M.L⁻¹ * ‖g‖) ^ 2 =
        M.L⁻¹ / 2 * ‖g‖ ^ 2 := by
    field_simp
  rw [hcoef] at hup
  have hnormsq : ‖g‖ ^ 2 ≤ 0 := by
    have hinvpos : 0 < M.L⁻¹ := inv_pos.mpr M.hL
    nlinarith
  have hnorm : ‖g‖ = 0 := by
    nlinarith [norm_nonneg g]
  have hg : g = 0 := norm_eq_zero.mp hnorm
  exact hg

end SmoothConvexModel

namespace StronglyConvexSmoothModel

/-- Positivity of the smoothness constant follows from `0 < μ < L`. -/
theorem hL (M : StronglyConvexSmoothModel E) : 0 < M.L :=
  lt_trans M.hμ M.hμL

/-- The manuscript ratio lies in `(0,1)`. -/
theorem q_unit (M : StronglyConvexSmoothModel E) : UnitRatio M.q := by
  constructor
  · exact div_pos M.hμ M.hL
  · exact (div_lt_one M.hL).mpr M.hμL

/-- A global minimizer of the strongly convex model has zero gradient. -/
theorem minimizer_grad_eq_zero
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) :
    M.grad xStar = 0 := by
  let S : SmoothConvexModel E := {
    f := M.f
    grad := M.grad
    L := M.L
    hL := M.hL
    lower := by
      intro x y
      have h := M.lower x y
      have hnonneg :
          0 ≤ (M.μ / 2) * ‖y - x‖ ^ 2 :=
        mul_nonneg (le_of_lt (half_pos M.hμ)) (sq_nonneg _)
      linarith
    upper := M.upper
  }
  exact S.minimizer_grad_eq_zero hxStar

/-- The shifted objective and gradient form a convex `(L - μ)`-smooth
first-order model. -/
noncomputable def transformedModel
    (M : StronglyConvexSmoothModel E) (xStar : E) :
    SmoothConvexModel E where
  f := M.shiftedF xStar
  grad := M.shiftedGrad xStar
  L := M.L - M.μ
  hL := sub_pos.mpr M.hμL
  lower := by
    intro x y
    have h := M.lower x y
    have hdecomp :
        y - xStar = (x - xStar) + (y - x) := by
      abel
    have hnorm :
        ‖y - xStar‖ ^ 2 =
          ‖x - xStar‖ ^ 2 +
            2 * ⟪x - xStar, y - x⟫_ℝ +
            ‖y - x‖ ^ 2 := by
      rw [hdecomp, norm_add_sq_real]
    have hinner :
        ⟪M.shiftedGrad xStar x, y - x⟫_ℝ =
          ⟪M.grad x, y - x⟫_ℝ -
            M.μ * ⟪x - xStar, y - x⟫_ℝ := by
      simp [shiftedGrad, inner_sub_left, real_inner_smul_left]
    rw [hinner]
    simp only [shiftedF]
    rw [hnorm]
    ring_nf at h ⊢
    linarith
  upper := by
    intro x y
    have h := M.upper x y
    have hdecomp :
        y - xStar = (x - xStar) + (y - x) := by
      abel
    have hnorm :
        ‖y - xStar‖ ^ 2 =
          ‖x - xStar‖ ^ 2 +
            2 * ⟪x - xStar, y - x⟫_ℝ +
            ‖y - x‖ ^ 2 := by
      rw [hdecomp, norm_add_sq_real]
    have hinner :
        ⟪M.shiftedGrad xStar x, y - x⟫_ℝ =
          ⟪M.grad x, y - x⟫_ℝ -
            M.μ * ⟪x - xStar, y - x⟫_ℝ := by
      simp [shiftedGrad, inner_sub_left, real_inner_smul_left]
    rw [hinner]
    simp only [shiftedF]
    rw [hnorm]
    ring_nf at h ⊢
    linarith

/-- The shifted objective is minimized at the original minimizer. -/
theorem transformed_minimizer
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) :
    (M.transformedModel xStar).IsMinimizer xStar := by
  intro x
  have hlower := M.lower xStar x
  rw [M.minimizer_grad_eq_zero hxStar] at hlower
  simp only [inner_zero_left] at hlower
  dsimp [transformedModel, shiftedF]
  simp
  linarith

end StronglyConvexSmoothModel

namespace Internal

/-- Public target I-A02: the quadratic transform belongs to
`F_{0,L-μ}` and is normalized at the minimizer. -/
theorem transformedMemF0
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) :
    ∃ T : SmoothConvexModel E,
      T.L = M.L - M.μ ∧
      (∀ x : E, T.f x = M.shiftedF xStar x) ∧
      (∀ x : E, T.grad x = M.shiftedGrad xStar x) ∧
      T.f xStar = 0 ∧ T.grad xStar = 0 := by
  refine ⟨M.transformedModel xStar, rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · simp [StronglyConvexSmoothModel.transformedModel,
      StronglyConvexSmoothModel.shiftedF]
  · exact
      (M.transformedModel xStar).minimizer_grad_eq_zero
        (M.transformed_minimizer hxStar)

end Internal

end ITEMf
