import LemniAcc.Discrete.Recurrence.ExistenceUnique
import LemniAcc.Lemniscatic.Integral

/-!
# The two finite bounds on the recurrence parameter

Only the strict finite-horizon inequalities used by the manuscript convergence
theorem are exposed here.  Bisection, monotonicity across horizons, and the
asymptotic limit are intentionally outside this module.
-/

open Set MeasureTheory
open scoped Interval

set_option autoImplicit false

namespace LemniAcc

lemma rho_decrement_le_invSqrt
    (N k : Nat) (hk : k ≤ N) :
    rho N k - rho N (k + 1) ≤ 1 / Real.sqrt (omega N) := by
  let v := canonicalCoefficients_valid N
  change
    (canonicalCoefficients N).rho k -
        (canonicalCoefficients N).rho (k + 1) ≤
      1 / Real.sqrt (canonicalCoefficients N).omega
  rw [v.rho_succ_eq_oneStep hk]
  exact oneStep_decrement_le_invSqrt (v.oneStep_domain hk)

lemma rho_first_decrement_lt_invSqrt
    {N : Nat} (hN : 1 ≤ N) :
    rho N 0 - rho N 1 < 1 / Real.sqrt (omega N) := by
  have hΩ : 0 < omega N := omega_pos N
  have hspos : 0 < Real.sqrt (omega N) := Real.sqrt_pos.2 hΩ
  have hssq : (Real.sqrt (omega N)) ^ 2 = omega N :=
    Real.sq_sqrt hΩ.le
  have hρ1pos : 0 < rho N 1 := rho_pos N 1 hN
  have hρ1le : rho N 1 ≤ 1 := rho_le_one N 1
  have hdelta : 0 < rho N 0 - rho N 1 := by
    exact sub_pos.mpr (rho_strict N 0 (Nat.zero_le N))
  have hrel := rho_recurrence N 0 (Nat.zero_le N)
  unfold OneStepRel at hrel
  have hrhs : rho N 0 * (1 - (rho N 1) ^ 2) < 1 := by
    rw [rho_zero]
    nlinarith [sq_pos_of_pos hρ1pos]
  have hsquare :
      (Real.sqrt (omega N) * (rho N 0 - rho N 1)) ^ 2 < 1 := by
    rw [mul_pow, hssq]
    nlinarith
  have hproduct0 :
      0 < Real.sqrt (omega N) * (rho N 0 - rho N 1) :=
    mul_pos hspos hdelta
  have hproduct :
      Real.sqrt (omega N) * (rho N 0 - rho N 1) < 1 := by
    nlinarith [sq_nonneg
      (Real.sqrt (omega N) * (rho N 0 - rho N 1) + 1)]
  rw [lt_div_iff₀ hspos]
  nlinarith

lemma rho_tail_drop_le
    {N m : Nat} (hm : m ≤ N) :
    rho N 1 - rho N (m + 1) ≤
      (m : ℝ) / Real.sqrt (omega N) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmN : m ≤ N := by omega
      have ih' := ih (by omega)
      have hstep := rho_decrement_le_invSqrt N (m + 1) (by omega)
      calc
        rho N 1 - rho N (m + 1 + 1) =
            (rho N 1 - rho N (m + 1)) +
              (rho N (m + 1) - rho N (m + 1 + 1)) := by ring
        _ ≤ (m : ℝ) / Real.sqrt (omega N) +
              1 / Real.sqrt (omega N) :=
            add_le_add ih' hstep
        _ = ((m + 1 : Nat) : ℝ) / Real.sqrt (omega N) := by
            norm_num
            ring

lemma omega_strict_upper
    {N : Nat} (hN : 1 ≤ N) :
    omega N < ((N + 1 : Nat) : ℝ) ^ 2 := by
  have hfirst := rho_first_decrement_lt_invSqrt hN
  have htail := rho_tail_drop_le (N := N) (m := N) le_rfl
  have htotal :
      1 < ((N + 1 : Nat) : ℝ) / Real.sqrt (omega N) := by
    calc
      1 = (rho N 0 - rho N 1) +
          (rho N 1 - rho N (N + 1)) := by
            rw [rho_zero, rho_terminal]
            ring
      _ < 1 / Real.sqrt (omega N) +
          (N : ℝ) / Real.sqrt (omega N) :=
            add_lt_add_of_lt_of_le hfirst htail
      _ = ((N + 1 : Nat) : ℝ) / Real.sqrt (omega N) := by
            norm_num
            ring
  have hspos : 0 < Real.sqrt (omega N) :=
    Real.sqrt_pos.2 (omega_pos N)
  have hslt : Real.sqrt (omega N) < ((N + 1 : Nat) : ℝ) := by
    have := (lt_div_iff₀ hspos).mp htotal
    simpa using this
  have hsnonneg : 0 ≤ Real.sqrt (omega N) := hspos.le
  have hNnonneg : 0 ≤ ((N + 1 : Nat) : ℝ) := by positivity
  have hsq : (Real.sqrt (omega N)) ^ 2 = omega N :=
    Real.sq_sqrt (omega_pos N).le
  nlinarith [mul_pos
    (sub_pos.mpr hslt)
    (add_pos_of_pos_of_nonneg hspos hNnonneg)]

lemma omegaKernel_intervalIntegrable_rho
    {N i j : Nat} (hi : i ≤ N + 1) (hj : j ≤ N + 1) :
    IntervalIntegrable Lemniscatic.omegaKernel volume (rho N i) (rho N j) := by
  apply Lemniscatic.omegaKernel_intervalIntegrable.mono
      (c := rho N i) (d := rho N j)
  · rw [uIcc_of_le zero_le_one]
    exact uIcc_subset_Icc
      ⟨rho_nonneg N i hi, rho_le_one N i⟩
      ⟨rho_nonneg N j hj, rho_le_one N j⟩
  · exact le_rfl

lemma rho_rectangle_eq_invSqrt
    (N k : Nat) (hk : k ≤ N) :
    (rho N k - rho N (k + 1)) /
        Real.sqrt (rho N k * (1 - (rho N (k + 1)) ^ 2)) =
      1 / Real.sqrt (omega N) := by
  have hdelta : 0 < rho N k - rho N (k + 1) :=
    sub_pos.mpr (rho_strict N k hk)
  have hspos : 0 < Real.sqrt (omega N) :=
    Real.sqrt_pos.2 (omega_pos N)
  have hrel := rho_recurrence N k hk
  unfold OneStepRel at hrel
  have hrad :
      Real.sqrt (rho N k * (1 - (rho N (k + 1)) ^ 2)) =
        Real.sqrt (omega N) * (rho N k - rho N (k + 1)) := by
    rw [← hrel, Real.sqrt_mul (omega_pos N).le,
      Real.sqrt_sq_eq_abs, abs_of_pos hdelta]
  rw [hrad]
  field_simp

lemma rho_rectangle_lt_integral
    (N k : Nat) (hk : k ≤ N) :
    1 / Real.sqrt (omega N) <
      ∫ x in rho N (k + 1)..rho N k, Lemniscatic.omegaKernel x := by
  have hcomp :=
    Lemniscatic.omegaKernel_constant_lt_integral
      (rho_nonneg N (k + 1) (Nat.succ_le_succ hk))
      (rho_strict N k hk)
      (rho_le_one N k)
  rw [rho_rectangle_eq_invSqrt N k hk] at hcomp
  exact hcomp

lemma rho_integral_lower_le
    {N m : Nat} (hm : m ≤ N + 1) :
    (m : ℝ) / Real.sqrt (omega N) ≤
      ∫ x in rho N m..rho N 0, Lemniscatic.omegaKernel x := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmN : m ≤ N := by omega
      have ih' := ih (by omega)
      have hstep := rho_rectangle_lt_integral N m hmN
      have hintStep :=
        omegaKernel_intervalIntegrable_rho
          (N := N) (i := m + 1) (j := m) (by omega) (by omega)
      have hintPrev :=
        omegaKernel_intervalIntegrable_rho
          (N := N) (i := m) (j := 0) (by omega) (Nat.zero_le _)
      calc
        (((m + 1 : Nat) : ℝ) / Real.sqrt (omega N)) =
            1 / Real.sqrt (omega N) +
              (m : ℝ) / Real.sqrt (omega N) := by
                norm_num
                ring
        _ ≤ (∫ x in rho N (m + 1)..rho N m,
              Lemniscatic.omegaKernel x) +
            ∫ x in rho N m..rho N 0,
              Lemniscatic.omegaKernel x :=
              add_le_add hstep.le ih'
        _ = ∫ x in rho N (m + 1)..rho N 0,
              Lemniscatic.omegaKernel x :=
            intervalIntegral.integral_add_adjacent_intervals hintStep hintPrev

lemma rho_integral_lower_strict
    {N m : Nat} (hm : m ≤ N) :
    (((m + 1 : Nat) : ℝ) / Real.sqrt (omega N)) <
      ∫ x in rho N (m + 1)..rho N 0, Lemniscatic.omegaKernel x := by
  have hprev := rho_integral_lower_le
    (N := N) (m := m) (hm.trans (Nat.le_succ N))
  have hstep := rho_rectangle_lt_integral N m hm
  have hintStep :=
    omegaKernel_intervalIntegrable_rho
      (N := N) (i := m + 1) (j := m) (by omega) (by omega)
  have hintPrev :=
    omegaKernel_intervalIntegrable_rho
      (N := N) (i := m) (j := 0) (by omega) (Nat.zero_le _)
  calc
    (((m + 1 : Nat) : ℝ) / Real.sqrt (omega N)) =
        1 / Real.sqrt (omega N) +
          (m : ℝ) / Real.sqrt (omega N) := by
            norm_num
            ring
    _ < (∫ x in rho N (m + 1)..rho N m,
          Lemniscatic.omegaKernel x) +
        ∫ x in rho N m..rho N 0,
          Lemniscatic.omegaKernel x :=
            add_lt_add_of_lt_of_le hstep hprev
    _ = ∫ x in rho N (m + 1)..rho N 0,
          Lemniscatic.omegaKernel x :=
        intervalIntegral.integral_add_adjacent_intervals hintStep hintPrev

lemma omega_strict_lower
    {N : Nat} (_hN : 1 ≤ N) :
    ((N + 1 : Nat) : ℝ) ^ 2 / Lemniscatic.varpi ^ 2 < omega N := by
  have hintegral :=
    rho_integral_lower_strict (N := N) (m := N) (le_rfl : N ≤ N)
  rw [rho_terminal, rho_zero,
    Lemniscatic.integral_omegaKernel_zero_one] at hintegral
  have hspos : 0 < Real.sqrt (omega N) :=
    Real.sqrt_pos.2 (omega_pos N)
  have hvpos : 0 < Lemniscatic.varpi := Lemniscatic.varpi_pos
  have hlinear :
      ((N + 1 : Nat) : ℝ) <
        Lemniscatic.varpi * Real.sqrt (omega N) := by
    have := (div_lt_iff₀ hspos).mp hintegral
    simpa [mul_comm] using this
  have hNpos : 0 < ((N + 1 : Nat) : ℝ) := by positivity
  have hrightpos :
      0 < Lemniscatic.varpi * Real.sqrt (omega N) :=
    mul_pos hvpos hspos
  have hsquare :
      ((N + 1 : Nat) : ℝ) ^ 2 <
        (Lemniscatic.varpi * Real.sqrt (omega N)) ^ 2 := by
    nlinarith [mul_pos
      (sub_pos.mpr hlinear)
      (add_pos hrightpos hNpos)]
  have hssq : (Real.sqrt (omega N)) ^ 2 = omega N :=
    Real.sq_sqrt (omega_pos N).le
  rw [mul_pow, hssq] at hsquare
  rw [div_lt_iff₀ (sq_pos_of_pos hvpos)]
  nlinarith

namespace Internal

/-- The two strict finite bounds on the unique recurrence parameter. -/
theorem omega_bounds
    {N : Nat} (hN : 1 ≤ N) :
    ((N + 1 : Nat) : ℝ) ^ 2 / Lemniscatic.varpi ^ 2 < omega N ∧
      omega N < ((N + 1 : Nat) : ℝ) ^ 2 :=
  ⟨omega_strict_lower hN, omega_strict_upper hN⟩

end Internal

end LemniAcc
