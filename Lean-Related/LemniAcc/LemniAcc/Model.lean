import LemniAcc.Spec.Model

/-!
# Smooth-convex model for lemniscate acceleration

This module fixes the analytic model shared by the discrete and continuous
proofs. Public paper-facing wrappers specialize to finite-dimensional Euclidean
spaces; supporting lemmas may use a general complete real inner-product space.
-/

open scoped InnerProductSpace
open Set
open InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace SmoothConvexModel

/-- A differentiable global minimizer is stationary. -/
theorem minimizer_grad_eq_zero
    (M : SmoothConvexModel E) {xStar : E} (hxStar : M.IsMinimizer xStar) :
    M.grad xStar = 0 := by
  have hlocal : IsLocalMin M.f xStar := Filter.Eventually.of_forall hxStar
  have hdual :
      toDual ℝ E (M.grad xStar) = 0 :=
    hlocal.hasFDerivAt_eq_zero (M.hasGradient xStar).hasFDerivAt
  exact (toDual ℝ E).injective (by simpa using hdual)

/-- The first-order supporting-hyperplane inequality for a differentiable
convex objective. -/
theorem firstOrder
    (M : SmoothConvexModel E) (x y : E) :
    M.f x + ⟪M.grad x, y - x⟫_ℝ ≤ M.f y := by
  let φ : ℝ → ℝ := fun t ↦ M.f (x + t • (y - x))
  have hconv : ConvexOn ℝ Set.univ φ := by
    simpa [φ, Function.comp_def, AffineMap.lineMap_apply_module', add_comm] using
      M.convex.comp_affineMap (AffineMap.lineMap x y)
  have hdiff : DifferentiableAt ℝ φ 0 := by
    dsimp [φ]
    exact (M.hasGradient (x + (0 : ℝ) • (y - x))).differentiableAt.comp 0 (by fun_prop)
  have hderiv : deriv φ 0 = ⟪M.grad x, y - x⟫_ℝ := by
    dsimp [φ]
    rw [DifferentiableAt.deriv_comp_add_smul
      (M.hasGradient (x + (0 : ℝ) • (y - x))).differentiableAt]
    rw [(M.hasGradient (x + (0 : ℝ) • (y - x))).hasFDerivAt.fderiv]
    simp
  have hslope :=
    hconv.deriv_le_slope (x := (0 : ℝ)) (y := 1) (by simp) (by simp)
      zero_lt_one hdiff
  rw [hderiv, slope_def_field] at hslope
  dsimp [φ] at hslope
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at hslope
  have hxy : x + (y - x) = y := by abel
  rw [hxy] at hslope
  linarith

/-- The fundamental theorem of calculus along an affine line, expressed
through the model gradient. -/
private theorem integral_gradient_line
    (M : SmoothConvexModel E) (x d : E) :
    (∫ t in (0 : ℝ)..1, ⟪M.grad (x + t • d), d⟫_ℝ) =
      M.f (x + d) - M.f x := by
  let φ : ℝ → ℝ := fun t ↦ M.f (x + t • d)
  let φ' : ℝ → ℝ := fun t ↦ ⟪M.grad (x + t • d), d⟫_ℝ
  have hdiff (t : ℝ) : DifferentiableAt ℝ φ t := by
    dsimp [φ]
    exact (M.hasGradient (x + t • d)).differentiableAt.comp t (by fun_prop)
  have hderiv (t : ℝ) : deriv φ t = φ' t := by
    dsimp [φ, φ']
    rw [DifferentiableAt.deriv_comp_add_smul
      (M.hasGradient (x + t • d)).differentiableAt]
    rw [(M.hasGradient (x + t • d)).hasFDerivAt.fderiv]
    rfl
  have hgrad : Continuous M.grad := M.gradLipschitz.continuous
  have hcont : Continuous φ' := by
    dsimp [φ']
    fun_prop
  have hFTC :=
    intervalIntegral.integral_deriv_eq_sub' (a := (0 : ℝ)) (b := 1) φ (funext hderiv)
      (fun t _ ↦ hdiff t) hcont.continuousOn
  dsimp [φ, φ'] at hFTC ⊢
  simpa using hFTC

/-- The descent lemma for an objective with Lipschitz gradient. -/
theorem descent
    (M : SmoothConvexModel E) (x y : E) :
    M.f y ≤ M.f x + ⟪M.grad x, y - x⟫_ℝ +
      ((M.L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  let d : E := y - x
  let ψ : ℝ → ℝ := fun t ↦ ⟪M.grad (x + t • d), d⟫_ℝ
  let q : ℝ → ℝ :=
    fun t ↦ ⟪M.grad x, d⟫_ℝ + t * ((M.L : ℝ) * ‖d‖ ^ 2)
  have hgrad : Continuous M.grad := M.gradLipschitz.continuous
  have hψcont : Continuous ψ := by
    dsimp [ψ]
    fun_prop
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ψ t ≤ q t := by
    have hlip :=
      M.gradLipschitz.dist_le_mul (x + t • d) x
    rw [dist_eq_norm, dist_eq_norm] at hlip
    have hpath : x + t • d - x = t • d := by abel
    rw [hpath, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hlip
    calc
      ψ t =
          ⟪M.grad x, d⟫_ℝ +
            ⟪M.grad (x + t • d) - M.grad x, d⟫_ℝ := by
              dsimp [ψ]
              rw [inner_sub_left]
              ring
      _ ≤ ⟪M.grad x, d⟫_ℝ +
            ‖M.grad (x + t • d) - M.grad x‖ * ‖d‖ := by
              have hinner :=
                real_inner_le_norm (M.grad (x + t • d) - M.grad x) d
              linarith
      _ ≤ ⟪M.grad x, d⟫_ℝ +
            ((M.L : ℝ) * (t * ‖d‖)) * ‖d‖ := by
              have hmul :=
                mul_le_mul_of_nonneg_right hlip (norm_nonneg d)
              linarith
      _ = q t := by
            dsimp [q]
            ring
  have hint :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
      (hψcont.intervalIntegrable 0 1) (hqcont.intervalIntegrable 0 1) hpoint
  have hqint :
      (∫ t in (0 : ℝ)..1, q t) =
        ⟪M.grad x, d⟫_ℝ + ((M.L : ℝ) / 2) * ‖d‖ ^ 2 := by
    have hc :
        IntervalIntegrable (fun _ : ℝ ↦ ⟪M.grad x, d⟫_ℝ)
          MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hl :
        IntervalIntegrable
          (fun t : ℝ ↦ t * ((M.L : ℝ) * ‖d‖ ^ 2))
          MeasureTheory.volume 0 1 :=
      (continuous_id.mul continuous_const).intervalIntegrable 0 1
    dsimp [q]
    rw [intervalIntegral.integral_add hc hl]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const]
    norm_num [integral_id]
    ring
  rw [hqint] at hint
  have hline := M.integral_gradient_line x d
  dsimp [ψ] at hint
  rw [hline] at hint
  have hxy : x + d = y := by
    dsimp [d]
    abel
  rw [hxy] at hint
  dsimp [d] at hint ⊢
  linarith

/-- The necessary smooth-convex interpolation inequality, in residual form. -/
theorem interpolationGap_nonneg
    (M : SmoothConvexModel E) (x y : E) :
    0 ≤ M.interpolationGap x y := by
  let Lr : ℝ := M.L
  let u : E := M.grad x - M.grad y
  let z : E := x - Lr⁻¹ • u
  have hLr : 0 < Lr := by
    dsimp [Lr]
    exact_mod_cast M.hL
  have hsupport := M.firstOrder y z
  have hdescent := M.descent x z
  have hcombine := hsupport.trans hdescent
  have hzy : z - y = (x - y) - Lr⁻¹ • u := by
    dsimp [z]
    abel
  have hzx : z - x = (-Lr⁻¹) • u := by
    dsimp [z]
    module
  have hnorm :
      ‖(-Lr⁻¹) • u‖ ^ 2 = Lr⁻¹ ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hLr)]
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
  have hcoef :
      Lr / 2 * (Lr⁻¹ ^ 2) = Lr⁻¹ / 2 := by
    field_simp
  have hcombine' :
      M.f y +
          (⟪M.grad y, x - y⟫_ℝ - Lr⁻¹ * ⟪M.grad y, u⟫_ℝ) ≤
        M.f x + (-Lr⁻¹) * ⟪M.grad x, u⟫_ℝ +
          (Lr / 2) * (Lr⁻¹ ^ 2 * ‖u‖ ^ 2) :=
    hcombine
  rw [← mul_assoc, hcoef] at hcombine'
  have huinnerScaled :=
    congrArg (fun r : ℝ ↦ Lr⁻¹ * r) huinner
  ring_nf at huinnerScaled
  have hbasic :
      M.f y + ⟪M.grad y, x - y⟫_ℝ ≤
        M.f x - (Lr⁻¹ / 2) * ‖u‖ ^ 2 := by
    linarith [hcombine', huinnerScaled]
  have hrecip : 1 / (2 * Lr) = Lr⁻¹ / 2 := by
    field_simp
  dsimp [interpolationGap]
  change
    0 ≤ M.f x - M.f y - ⟪M.grad y, x - y⟫_ℝ -
      (1 / (2 * Lr)) * ‖u‖ ^ 2
  rw [hrecip]
  linarith

/-- The paper-facing orientation of the necessary pairwise interpolation
inequality. -/
theorem interpolation
    (M : SmoothConvexModel E) (x y : E) :
    M.f y + ⟪M.grad y, x - y⟫_ℝ +
        (1 / (2 * (M.L : ℝ))) * ‖M.grad x - M.grad y‖ ^ 2 ≤
      M.f x := by
  have hgap := M.interpolationGap_nonneg x y
  dsimp [interpolationGap] at hgap
  linarith

end SmoothConvexModel

end LemniAcc
