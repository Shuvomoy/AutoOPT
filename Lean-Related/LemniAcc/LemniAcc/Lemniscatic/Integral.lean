import Mathlib

/-!
# The lemniscatic integral

This module defines the inverse-integral coordinate used by lemniscate
acceleration.  The endpoint singularity is harmless in the Lebesgue integral:
on `[0,1]` the density is dominated by the integrable Chebyshev density
`(1 - x²)⁻¹/²`.
-/

open scoped Interval
open Set MeasureTheory intervalIntegral

set_option autoImplicit false

namespace LemniAcc.Lemniscatic

/-- The density in the defining integral of the lemniscatic sine. -/
noncomputable def arcslIntegrand (x : ℝ) : ℝ :=
  (Real.sqrt (1 - x ^ 4))⁻¹

/-- The inverse coordinate whose inverse on `[0,1]` is the lemniscatic sine. -/
noncomputable def arcsl (u : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..u, arcslIntegrand x

/-- The lemniscate constant `varpi = 2 ∫₀¹ (1-x⁴)⁻¹/² dx`. -/
noncomputable def varpi : ℝ :=
  2 * arcsl 1

/-- The comparison kernel appearing in the finite omega bound. -/
noncomputable def omegaKernel (x : ℝ) : ℝ :=
  (Real.sqrt (x * (1 - x ^ 2)))⁻¹

@[simp] theorem arcsl_zero : arcsl 0 = 0 := by
  simp [arcsl]

theorem varpi_eq_two_mul_integral :
    varpi = 2 * ∫ x in (0 : ℝ)..1, arcslIntegrand x := by
  rfl

theorem arcsl_one : arcsl 1 = varpi / 2 := by
  rw [varpi]
  ring

theorem arcslIntegrand_nonneg (x : ℝ) : 0 ≤ arcslIntegrand x := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem arcslIntegrand_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < arcslIntegrand x := by
  have hx_sq : x ^ 2 < 1 := by
    rw [sq_lt_one_iff_abs_lt_one, abs_lt]
    exact hx
  have hx_four : x ^ 4 < 1 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ < 1 := (sq_lt_one_iff₀ (sq_nonneg x)).2 hx_sq
  exact inv_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hx_four))

theorem arcslIntegrand_continuousAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt arcslIntegrand x := by
  have hx_sq : x ^ 2 < 1 := by
    rw [sq_lt_one_iff_abs_lt_one, abs_lt]
    exact hx
  have hx_four : x ^ 4 < 1 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ < 1 := (sq_lt_one_iff₀ (sq_nonneg x)).2 hx_sq
  have hsqrt : Real.sqrt (1 - x ^ 4) ≠ 0 :=
    (Real.sqrt_pos.2 (sub_pos.mpr hx_four)).ne'
  exact
    ((Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_id.pow 4))).continuousAt.inv₀ hsqrt)

theorem arcslIntegrand_intervalIntegrable :
    IntervalIntegrable arcslIntegrand volume (0 : ℝ) 1 := by
  have hchebRaw :=
    Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv.mono
      (c := (0 : ℝ)) (d := 1)
      (by
        rw [uIcc_of_le zero_le_one, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        exact Icc_subset_Icc (by norm_num) le_rfl)
      le_rfl
  have hcheb :
      IntervalIntegrable (fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹)
        volume (0 : ℝ) 1 := by
    simpa only [Real.sqrt_inv] using hchebRaw
  refine hcheb.mono_fun (by unfold arcslIntegrand; fun_prop) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (arcslIntegrand_nonneg x),
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  by_cases hx_sq : x ^ 2 < 1
  · have hx_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
    have hx_four_le_sq : x ^ 4 ≤ x ^ 2 := by
      nlinarith [mul_nonneg hx_sq_nonneg (sub_nonneg.mpr hx_sq.le)]
    have hsqrt :
        Real.sqrt (1 - x ^ 2) ≤ Real.sqrt (1 - x ^ 4) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hpos2 : 0 < Real.sqrt (1 - x ^ 2) :=
      Real.sqrt_pos.2 (by nlinarith)
    have hpos4 : 0 < Real.sqrt (1 - x ^ 4) :=
      Real.sqrt_pos.2 (by nlinarith)
    simpa [arcslIntegrand] using (inv_le_inv₀ hpos4 hpos2).2 hsqrt
  · have hx_sq_ge : 1 ≤ x ^ 2 := le_of_not_gt hx_sq
    have hfactor :
        0 ≤ (x ^ 2 + 1) * (x ^ 2 - 1) :=
      mul_nonneg (by nlinarith [sq_nonneg x]) (by linarith)
    have htwo : Real.sqrt (1 - x ^ 2) = 0 :=
      Real.sqrt_eq_zero'.2 (by linarith)
    have hfour : Real.sqrt (1 - x ^ 4) = 0 :=
      Real.sqrt_eq_zero'.2 (by nlinarith)
    simp [arcslIntegrand, htwo, hfour]

private theorem omegaKernel_sq_mul {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    omegaKernel (x ^ 2) * (2 * x) = 2 * arcslIntegrand x := by
  rcases eq_or_lt_of_le hx1 with rfl | hxlt
  · simp [omegaKernel, arcslIntegrand]
  have hx_sq : x ^ 2 < 1 :=
    (sq_lt_one_iff₀ hx0.le).2 hxlt
  have hx_four : x ^ 4 < 1 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ < 1 := (sq_lt_one_iff₀ (sq_nonneg x)).2 hx_sq
  have hsqrt : Real.sqrt (1 - x ^ 4) ≠ 0 :=
    (Real.sqrt_pos.2 (sub_pos.mpr hx_four)).ne'
  have hxne : x ≠ 0 := hx0.ne'
  rw [omegaKernel, arcslIntegrand]
  have hrad :
      Real.sqrt (x ^ 2 * (1 - (x ^ 2) ^ 2)) =
        x * Real.sqrt (1 - x ^ 4) := by
    rw [show x ^ 2 * (1 - (x ^ 2) ^ 2) = x ^ 2 * (1 - x ^ 4) by ring,
      Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx0]
  rw [hrad]
  field_simp

theorem omegaKernel_intervalIntegrable :
    IntervalIntegrable omegaKernel volume (0 : ℝ) 1 := by
  have htrans :
      IntervalIntegrable
        (fun x : ℝ => (omegaKernel ∘ fun y : ℝ => y ^ 2) x * (2 * x))
        volume (0 : ℝ) 1 := by
    have htwo :
        IntervalIntegrable (fun x : ℝ => 2 * arcslIntegrand x)
          volume (0 : ℝ) 1 :=
      arcslIntegrand_intervalIntegrable.const_mul 2
    exact htwo.congr_uIoo (fun x hx => by
      have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
      exact (omegaKernel_sq_mul hx'.1 hx'.2.le).symm)
  have hiff :=
    intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (a := (0 : ℝ)) (b := 1)
      (f := fun x : ℝ => x ^ 2) (f' := fun x : ℝ => 2 * x)
      (g := omegaKernel)
      (by fun_prop)
      (fun x _ => by
        simpa [pow_two] using! (hasDerivAt_id' x).pow 2)
      (fun x hx => by
        have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
        exact mul_nonneg (by norm_num) hx'.1.le)
  simpa using hiff.mp htrans

theorem integral_omegaKernel_zero_one :
    (∫ x in (0 : ℝ)..1, omegaKernel x) = varpi := by
  have hsubst :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := 1)
      (f := fun x : ℝ => x ^ 2) (f' := fun x : ℝ => 2 * x)
      (g := omegaKernel)
      (by fun_prop)
      (fun x _ => by
        simpa [pow_two] using! (hasDerivAt_id' x).pow 2)
      (fun x hx => by
        have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
        exact mul_nonneg (by norm_num) hx'.1.le)
  have hleft :
      (∫ x in (0 : ℝ)..1,
          (omegaKernel ∘ fun y : ℝ => y ^ 2) x * (2 * x)) =
        ∫ x in (0 : ℝ)..1, 2 * arcslIntegrand x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [uIoc_of_le zero_le_one] at hx
    exact omegaKernel_sq_mul hx.1 hx.2
  rw [hleft] at hsubst
  norm_num at hsubst
  calc
    (∫ x in (0 : ℝ)..1, omegaKernel x) =
        2 * ∫ x in (0 : ℝ)..1, arcslIntegrand x := hsubst.symm
    _ = varpi := varpi_eq_two_mul_integral.symm

/-- The strict interval comparison used in the finite lower bound on
`Omega_N`.  The constant on the left is the endpoint rectangle that the
kernel strictly dominates in the interior. -/
theorem omegaKernel_constant_lt_integral
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ 1) :
    (a - b) / Real.sqrt (a * (1 - b ^ 2)) <
      ∫ x in b..a, omegaKernel x := by
  have ha0 : 0 < a := lt_of_le_of_lt hb hba
  have hb1 : b < 1 := hba.trans_le ha
  have hbsq : b ^ 2 < 1 := (sq_lt_one_iff₀ hb).2 hb1
  have hmax_pos : 0 < Real.sqrt (a * (1 - b ^ 2)) := by
    apply Real.sqrt_pos.2
    exact mul_pos ha0 (sub_pos.mpr hbsq)
  have hker : IntervalIntegrable omegaKernel volume b a :=
    omegaKernel_intervalIntegrable.mono
      (c := b) (d := a)
      (by
        rw [uIcc_of_le hba.le, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc hb ha)
      le_rfl
  let c : ℝ := (Real.sqrt (a * (1 - b ^ 2)))⁻¹
  have hdiff :
      IntervalIntegrable (fun x : ℝ => omegaKernel x - c) volume b a :=
    hker.sub intervalIntegrable_const
  have hpos : ∀ x : ℝ, x ∈ Ioo b a → 0 < omegaKernel x - c := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt hb hx.1
    have hx1 : x < 1 := hx.2.trans_le ha
    have hxsq : x ^ 2 < 1 := (sq_lt_one_iff₀ hx0.le).2 hx1
    have hbsq_xsq : b ^ 2 < x ^ 2 := by
      have hprod : 0 < (x - b) * (x + b) :=
        mul_pos (sub_pos.mpr hx.1) (by linarith)
      nlinarith
    have hrad :
        x * (1 - x ^ 2) < a * (1 - b ^ 2) := by
      calc
        x * (1 - x ^ 2) < a * (1 - x ^ 2) :=
          mul_lt_mul_of_pos_right hx.2 (sub_pos.mpr hxsq)
        _ < a * (1 - b ^ 2) :=
          mul_lt_mul_of_pos_left (by linarith) ha0
    have hcur_pos : 0 < Real.sqrt (x * (1 - x ^ 2)) := by
      apply Real.sqrt_pos.2
      exact mul_pos hx0 (sub_pos.mpr hxsq)
    have hsqrt :
        Real.sqrt (x * (1 - x ^ 2)) <
          Real.sqrt (a * (1 - b ^ 2)) :=
      Real.sqrt_lt_sqrt (mul_nonneg hx0.le (sub_nonneg.mpr hxsq.le)) hrad
    have hinv :
        (Real.sqrt (a * (1 - b ^ 2)))⁻¹ <
          (Real.sqrt (x * (1 - x ^ 2)))⁻¹ :=
      (inv_lt_inv₀ hmax_pos hcur_pos).2 hsqrt
    simpa [omegaKernel, c, sub_pos] using hinv
  have hint_pos :
      0 < ∫ x in b..a, (omegaKernel x - c) :=
    intervalIntegral_pos_of_pos_on hdiff hpos hba
  rw [intervalIntegral.integral_sub hker intervalIntegrable_const] at hint_pos
  have hconst :
      (∫ _x : ℝ in b..a, c) = (a - b) * c := by simp
  rw [hconst] at hint_pos
  simpa [c, div_eq_mul_inv, sub_pos] using hint_pos

theorem varpi_pos : 0 < varpi := by
  rw [varpi_eq_two_mul_integral]
  have hint_pos : 0 < ∫ x in (0 : ℝ)..1, arcslIntegrand x :=
    intervalIntegral_pos_of_pos_on arcslIntegrand_intervalIntegrable
      (fun x hx => arcslIntegrand_pos ⟨by linarith [hx.1], hx.2⟩) zero_lt_one
  positivity

end LemniAcc.Lemniscatic
