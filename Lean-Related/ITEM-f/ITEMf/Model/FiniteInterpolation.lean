import ITEMf.Spec.Model

/-!
# Core inequality
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace SmoothConvexModel

/-- Every pair of samples from an actual smooth-convex first-order model
satisfies the interpolation residual inequality. -/
theorem interpolationGap_nonneg
    (M : SmoothConvexModel E) (x y : E) :
    0 ≤ M.interpolationGap x y := by
  let u : E := M.grad x - M.grad y
  let z : E := x - M.L⁻¹ • u
  have hL : M.L ≠ 0 := ne_of_gt M.hL
  have hlower := M.lower y z
  have hupper := M.upper x z
  have hcombine := hlower.trans hupper
  have hzy : z - y = (x - y) - M.L⁻¹ • u := by
    dsimp [z]
    abel
  have hzx : z - x = (-M.L⁻¹) • u := by
    dsimp [z]
    module
  have hnorm :
      ‖(-M.L⁻¹) • u‖ ^ 2 = M.L⁻¹ ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr M.hL)]
    ring
  have huinner :
      ⟪M.grad x, u⟫_ℝ - ⟪M.grad y, u⟫_ℝ = ‖u‖ ^ 2 := by
    calc
      ⟪M.grad x, u⟫_ℝ - ⟪M.grad y, u⟫_ℝ =
          ⟪M.grad x - M.grad y, u⟫_ℝ := by
            rw [inner_sub_left]
      _ = ⟪u, u⟫_ℝ := by rfl
      _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  rw [hzy, hzx, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right, hnorm] at hcombine
  have hcoef : M.L / 2 * M.L⁻¹ ^ 2 = M.L⁻¹ / 2 := by
    field_simp
  have hcombine' :
      M.f y +
          (⟪M.grad y, x - y⟫_ℝ - M.L⁻¹ * ⟪M.grad y, u⟫_ℝ) ≤
        M.f x + (-M.L⁻¹) * ⟪M.grad x, u⟫_ℝ +
          (M.L / 2) * (M.L⁻¹ ^ 2 * ‖u‖ ^ 2) :=
    hcombine
  rw [← mul_assoc, hcoef] at hcombine'
  have huinnerScaled :=
    congrArg (fun r : ℝ ↦ M.L⁻¹ * r) huinner
  ring_nf at huinnerScaled
  have hbasic :
      M.f y + ⟪M.grad y, x - y⟫_ℝ ≤
        M.f x - (M.L⁻¹ / 2) * ‖u‖ ^ 2 := by
    linarith [hcombine', huinnerScaled]
  have hrecip : 1 / (2 * M.L) = M.L⁻¹ / 2 := by
    field_simp
  dsimp [interpolationGap]
  change
    0 ≤ M.f x - M.f y - ⟪M.grad y, x - y⟫_ℝ -
      (1 / (2 * M.L)) * ‖u‖ ^ 2
  rw [hrecip]
  linarith

end SmoothConvexModel

namespace Internal

/-- The core inequality. -/
theorem finiteInterpolation
    {d n : Nat}
    (M : SmoothConvexModel (Euclidean d))
    (x : Fin n → Euclidean d) :
    ∀ i j : Fin n,
      M.f (x j) + ⟪M.grad (x j), x i - x j⟫_ℝ +
          (1 / (2 * M.L)) *
            ‖M.grad (x i) - M.grad (x j)‖ ^ 2 ≤
        M.f (x i) := by
  intro i j
  have hgap := M.interpolationGap_nonneg (x i) (x j)
  dsimp [SmoothConvexModel.interpolationGap] at hgap
  linarith

end Internal

end ITEMf
