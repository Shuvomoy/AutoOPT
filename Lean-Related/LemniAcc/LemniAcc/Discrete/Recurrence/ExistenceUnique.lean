import LemniAcc.Discrete.Recurrence.OneStep

/-!
# Existence and uniqueness of the finite recurrence

For a fixed horizon, the total clipped one-step map gives a continuous
shooting orbit on `Ω ≥ 1`.  An intermediate-value argument chooses the unique
parameter whose last positive entry equals `1 / Ω`; the following clipped
step is then zero.
-/

open Set

set_option autoImplicit false

namespace LemniAcc

/-- Coefficient data, extended by zero after the finite horizon. -/
structure CoefficientData (N : Nat) where
  omega : ℝ
  rho : Nat → ℝ

/-- The exact finite recurrence and its endpoint/order conditions. -/
structure ValidCoefficients (N : Nat) (c : CoefficientData N) : Prop where
  omega_pos : 0 < c.omega
  rho_zero : c.rho 0 = 1
  rho_terminal : c.rho (N + 1) = 0
  rho_nonneg : ∀ k, k ≤ N + 1 → 0 ≤ c.rho k
  rho_strict : ∀ k, k ≤ N → c.rho (k + 1) < c.rho k
  recurrence : ∀ k, k ≤ N →
    OneStepRel c.omega (c.rho k) (c.rho (k + 1))
  rho_tail : ∀ k, N + 1 ≤ k → c.rho k = 0

/-- The clipped shooting orbit from the left endpoint `1`. -/
noncomputable def shooting (Ω : ℝ) : Nat → ℝ
  | 0 => 1
  | k + 1 => oneStep Ω (shooting Ω k)

@[simp] lemma shooting_zero (Ω : ℝ) : shooting Ω 0 = 1 := rfl

@[simp] lemma shooting_succ (Ω : ℝ) (k : Nat) :
    shooting Ω (k + 1) = oneStep Ω (shooting Ω k) := rfl

lemma shooting_mem_Icc
    {Ω : ℝ} (hΩ : 1 ≤ Ω) (k : Nat) :
    shooting Ω k ∈ Icc (0 : ℝ) 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      simpa only [shooting_succ] using oneStep_mem_Icc hΩ ih

lemma shooting_nonneg
    {Ω : ℝ} (hΩ : 1 ≤ Ω) (k : Nat) :
    0 ≤ shooting Ω k :=
  (shooting_mem_Icc hΩ k).1

lemma shooting_le_one
    {Ω : ℝ} (hΩ : 1 ≤ Ω) (k : Nat) :
    shooting Ω k ≤ 1 :=
  (shooting_mem_Icc hΩ k).2

lemma shooting_antitone_step
    {Ω : ℝ} (hΩ : 1 ≤ Ω) (k : Nat) :
    shooting Ω (k + 1) ≤ shooting Ω k := by
  rw [shooting_succ]
  exact oneStep_le hΩ (shooting_nonneg hΩ k) (shooting_le_one hΩ k)

lemma shooting_antitone
    {Ω : ℝ} (hΩ : 1 ≤ Ω) :
    Antitone (shooting Ω) := by
  exact antitone_nat_of_succ_le (shooting_antitone_step hΩ)

lemma shooting_continuousOn (k : Nat) :
    ContinuousOn (fun Ω : ℝ => shooting Ω k) (Ici (1 : ℝ)) := by
  induction k with
  | zero => exact continuousOn_const
  | succ k ih =>
      rw [show (fun Ω : ℝ => shooting Ω (k + 1)) =
          (fun p : ℝ × ℝ => oneStep p.1 p.2) ∘
            (fun Ω : ℝ => (Ω, shooting Ω k)) by
        funext Ω
        simp]
      apply continuousOn_oneStep.comp (continuousOn_id.prodMk ih)
      intro Ω hΩ
      exact ⟨hΩ, shooting_mem_Icc hΩ k⟩

lemma shooting_one_succ (k : Nat) :
    shooting 1 (k + 1) = 0 := by
  induction k with
  | zero =>
      norm_num [shooting, oneStep, oneStepRaw, oneStepDiscriminant]
  | succ k ih =>
      change oneStep 1 (shooting 1 (k + 1)) = 0
      rw [ih]
      norm_num [oneStep, oneStepRaw, oneStepDiscriminant]

lemma shooting_eq_oneStep_of_domain
    {Ω : ℝ} (hΩ : 1 ≤ Ω) {k : Nat}
    (hprod : 1 ≤ Ω * shooting Ω k) :
    OneStepDomain Ω (shooting Ω k) := by
  have hΩpos : 0 < Ω := zero_lt_one.trans_le hΩ
  have hrpos : 0 < shooting Ω k := by
    by_contra hnot
    have hrnonneg := shooting_nonneg hΩ k
    have hz : shooting Ω k = 0 := le_antisymm (le_of_not_gt hnot) hrnonneg
    rw [hz] at hprod
    norm_num at hprod
  exact ⟨hΩpos, hrpos, shooting_le_one hΩ k, hprod⟩

lemma shooting_rel_of_domain
    {Ω : ℝ} (hΩ : 1 ≤ Ω) {k : Nat}
    (hprod : 1 ≤ Ω * shooting Ω k) :
    OneStepRel Ω (shooting Ω k) (shooting Ω (k + 1)) := by
  rw [shooting_succ]
  exact oneStep_rel (shooting_eq_oneStep_of_domain hΩ hprod)

lemma shooting_strict_step_of_domain
    {Ω : ℝ} (hΩ : 1 ≤ Ω) {k : Nat}
    (hprod : 1 ≤ Ω * shooting Ω k) :
    shooting Ω (k + 1) < shooting Ω k := by
  rw [shooting_succ]
  exact oneStep_lt (shooting_eq_oneStep_of_domain hΩ hprod)

lemma shooting_decrement_le_invSqrt
    {Ω : ℝ} (hΩ : 1 ≤ Ω) {k : Nat}
    (hprod : 1 ≤ Ω * shooting Ω k) :
    shooting Ω k - shooting Ω (k + 1) ≤ 1 / Real.sqrt Ω := by
  rw [shooting_succ]
  exact oneStep_decrement_le_invSqrt
    (shooting_eq_oneStep_of_domain hΩ hprod)

/-- A shot cannot descend faster than one reciprocal square-root per step. -/
lemma shooting_lower_bound
    {Ω : ℝ} (hΩ : 1 ≤ Ω) (k : Nat)
    (hk : (k : ℝ) ≤ Real.sqrt Ω) :
    (Real.sqrt Ω - (k : ℝ)) / Real.sqrt Ω ≤ shooting Ω k := by
  have hΩpos : 0 < Ω := zero_lt_one.trans_le hΩ
  have hspos : 0 < Real.sqrt Ω := Real.sqrt_pos.2 hΩpos
  have hs0 : 0 ≤ Real.sqrt Ω := hspos.le
  have hsne : Real.sqrt Ω ≠ 0 := ne_of_gt hspos
  have hssq : (Real.sqrt Ω) ^ 2 = Ω := Real.sq_sqrt hΩpos.le
  induction k with
  | zero =>
      simp only [Nat.cast_zero, sub_zero, shooting_zero]
      exact le_of_eq (div_self hsne)
  | succ k ih =>
      have hk' : (k : ℝ) ≤ Real.sqrt Ω := by
        norm_num at hk ⊢
        linarith
      have ih' := ih hk'
      have hscaled :
          Real.sqrt Ω - (k : ℝ) ≤
            Real.sqrt Ω * shooting Ω k := by
        have hmul := mul_le_mul_of_nonneg_left ih' hs0
        have hcancel :
            Real.sqrt Ω *
                ((Real.sqrt Ω - (k : ℝ)) / Real.sqrt Ω) =
              Real.sqrt Ω - (k : ℝ) := by
          field_simp
        rwa [hcancel] at hmul
      have hgap : 1 ≤ Real.sqrt Ω - (k : ℝ) := by
        norm_num at hk
        linarith
      have hs1 : 1 ≤ Real.sqrt Ω := by
        have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
        linarith
      have hone :
          1 ≤ Real.sqrt Ω * (Real.sqrt Ω - (k : ℝ)) := by
        have hprod :
            0 ≤ (Real.sqrt Ω - 1) *
              (Real.sqrt Ω - (k : ℝ) - 1) :=
          mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hgap)
        nlinarith
      have hprod : 1 ≤ Ω * shooting Ω k := by
        have hmul := mul_le_mul_of_nonneg_left hscaled hs0
        have hid :
            Real.sqrt Ω * (Real.sqrt Ω * shooting Ω k) =
              Ω * shooting Ω k := by
          calc
            Real.sqrt Ω * (Real.sqrt Ω * shooting Ω k) =
                (Real.sqrt Ω) ^ 2 * shooting Ω k := by ring
            _ = Ω * shooting Ω k := by rw [hssq]
        rw [hid] at hmul
        exact hone.trans hmul
      have hdec := shooting_decrement_le_invSqrt hΩ hprod
      have hsplit :
          (Real.sqrt Ω - ((k + 1 : Nat) : ℝ)) / Real.sqrt Ω =
            (Real.sqrt Ω - (k : ℝ)) / Real.sqrt Ω -
              1 / Real.sqrt Ω := by
        norm_num
        field_simp
        ring
      rw [hsplit]
      linarith

lemma shooting_upper_horizon_lower
    (N : Nat) :
    1 / ((N + 1 : Nat) : ℝ) ≤
      shooting (((N + 1 : Nat) : ℝ) ^ 2) N := by
  let B : ℝ := ((N + 1 : Nat) : ℝ)
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hsqrt : Real.sqrt (B ^ 2) = B := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hBpos]
  have hΩ : 1 ≤ B ^ 2 := by
    have hB1 : 1 ≤ B := by
      dsimp [B]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    nlinarith [sq_nonneg (B - 1)]
  have hk : (N : ℝ) ≤ Real.sqrt (B ^ 2) := by
    rw [hsqrt]
    dsimp [B]
    norm_num
  have hbound := shooting_lower_bound hΩ N hk
  rw [hsqrt] at hbound
  change 1 / B ≤ shooting (B ^ 2) N
  have hid : (B - (N : ℝ)) / B = 1 / B := by
    congr 1
    dsimp [B]
    norm_num
  rwa [hid] at hbound

/-- The terminal shooting residual before the final zero step. -/
noncomputable def shootingResidual (N : Nat) (Ω : ℝ) : ℝ :=
  Ω * shooting Ω N

lemma shootingResidual_continuousOn (N : Nat) :
    ContinuousOn (shootingResidual N) (Ici (1 : ℝ)) := by
  unfold shootingResidual
  exact continuousOn_id.mul (shooting_continuousOn N)

lemma shootingResidual_one
    {N : Nat} (hN : 1 ≤ N) :
    shootingResidual N 1 = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  unfold shootingResidual
  rw [show 1 + m = m + 1 by omega, shooting_one_succ]
  norm_num

lemma shootingResidual_upper
    {N : Nat} (hN : 1 ≤ N) :
    1 < shootingResidual N (((N + 1 : Nat) : ℝ) ^ 2) := by
  let B : ℝ := ((N + 1 : Nat) : ℝ)
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hlower : 1 / B ≤ shooting (B ^ 2) N := by
    simpa only [B] using shooting_upper_horizon_lower N
  have hmul :
      B ^ 2 * (1 / B) ≤ B ^ 2 * shooting (B ^ 2) N :=
    mul_le_mul_of_nonneg_left hlower (sq_nonneg B)
  have hcancel : B ^ 2 * (1 / B) = B := by
    field_simp
  have hB : 1 < B := by
    dsimp [B]
    exact_mod_cast Nat.succ_lt_succ hN
  unfold shootingResidual
  change 1 < B ^ 2 * shooting (B ^ 2) N
  rw [hcancel] at hmul
  exact hB.trans_le hmul

lemma exists_shooting_parameter
    {N : Nat} (hN : 1 ≤ N) :
    ∃ Ω ∈ Icc (1 : ℝ) (((N + 1 : Nat) : ℝ) ^ 2),
      shootingResidual N Ω = 1 := by
  let U : ℝ := ((N + 1 : Nat) : ℝ) ^ 2
  have hU : 1 ≤ U := by
    dsimp [U]
    have h : (1 : ℝ) ≤ ((N + 1 : Nat) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    nlinarith [sq_nonneg (((N + 1 : Nat) : ℝ) - 1)]
  have hcont : ContinuousOn (shootingResidual N) (Icc (1 : ℝ) U) :=
    (shootingResidual_continuousOn N).mono (Icc_subset_Ici_self)
  have hlow : shootingResidual N 1 ≤ 1 := by
    rw [shootingResidual_one hN]
    norm_num
  have hupp : 1 ≤ shootingResidual N U := by
    exact (by
      dsimp [U]
      exact (shootingResidual_upper hN).le)
  have himage :=
    intermediate_value_Icc hU hcont (show (1 : ℝ) ∈
      Icc (shootingResidual N 1) (shootingResidual N U) from ⟨hlow, hupp⟩)
  rcases himage with ⟨Ω, hΩ, hres⟩
  exact ⟨Ω, hΩ, hres⟩

/-- The shot, cut off after its prescribed terminal index. -/
noncomputable def shootingData (N : Nat) (Ω : ℝ) : CoefficientData N where
  omega := Ω
  rho k := if k ≤ N + 1 then shooting Ω k else 0

@[simp] lemma shootingData_omega (N : Nat) (Ω : ℝ) :
    (shootingData N Ω).omega = Ω := rfl

lemma shootingData_rho_of_le
    {N k : Nat} {Ω : ℝ} (hk : k ≤ N + 1) :
    (shootingData N Ω).rho k = shooting Ω k := by
  simp [shootingData, hk]

lemma shootingData_rho_of_lt
    {N k : Nat} {Ω : ℝ} (hk : N + 1 < k) :
    (shootingData N Ω).rho k = 0 := by
  simp [shootingData, Nat.not_le_of_lt hk]

lemma shooting_terminal_of_residual
    {N : Nat} {Ω : ℝ} (hΩ : 1 ≤ Ω)
    (hres : shootingResidual N Ω = 1) :
    shooting Ω (N + 1) = 0 := by
  have hprod : Ω * shooting Ω N = 1 := hres
  have hdom := shooting_eq_oneStep_of_domain hΩ hprod.symm.le
  rw [shooting_succ, oneStep_eq_zero_iff hdom]
  exact hprod

lemma shooting_product_ge_of_residual
    {N k : Nat} {Ω : ℝ} (hΩ : 1 ≤ Ω)
    (hres : shootingResidual N Ω = 1) (hk : k ≤ N) :
    1 ≤ Ω * shooting Ω k := by
  have hmono : shooting Ω N ≤ shooting Ω k :=
    shooting_antitone hΩ hk
  have hmul := mul_le_mul_of_nonneg_left hmono (zero_le_one.trans hΩ)
  unfold shootingResidual at hres
  linarith

lemma shootingData_valid_of_residual
    {N : Nat} {Ω : ℝ} (hΩ : 1 ≤ Ω)
    (hres : shootingResidual N Ω = 1) :
    ValidCoefficients N (shootingData N Ω) := by
  have hterm : shooting Ω (N + 1) = 0 :=
    shooting_terminal_of_residual hΩ hres
  refine
    { omega_pos := zero_lt_one.trans_le hΩ
      rho_zero := by simp [shootingData]
      rho_terminal := by
        rw [shootingData_rho_of_le (le_rfl : N + 1 ≤ N + 1)]
        exact hterm
      rho_nonneg := ?_
      rho_strict := ?_
      recurrence := ?_
      rho_tail := ?_ }
  · intro k hk
    rw [shootingData_rho_of_le hk]
    exact shooting_nonneg hΩ k
  · intro k hk
    rw [shootingData_rho_of_le (Nat.succ_le_succ hk),
      shootingData_rho_of_le (hk.trans (Nat.le_succ N))]
    exact shooting_strict_step_of_domain hΩ
      (shooting_product_ge_of_residual hΩ hres hk)
  · intro k hk
    rw [shootingData_rho_of_le (Nat.succ_le_succ hk),
      shootingData_rho_of_le (hk.trans (Nat.le_succ N))]
    exact shooting_rel_of_domain hΩ
      (shooting_product_ge_of_residual hΩ hres hk)
  · intro k hk
    rcases hk.eq_or_lt with rfl | hk'
    · rw [shootingData_rho_of_le (le_rfl : N + 1 ≤ N + 1)]
      exact hterm
    · exact shootingData_rho_of_lt hk'

lemma validCoefficients_zero :
    ValidCoefficients 0
      { omega := 1
        rho := fun k => if k = 0 then 1 else 0 } := by
  refine
    { omega_pos := zero_lt_one
      rho_zero := by simp
      rho_terminal := by simp
      rho_nonneg := ?_
      rho_strict := ?_
      recurrence := ?_
      rho_tail := ?_ }
  · intro k hk
    interval_cases k <;> simp
  · intro k hk
    interval_cases k
    norm_num
  · intro k hk
    interval_cases k
    norm_num [OneStepRel]
  · intro k hk
    have : k ≠ 0 := by omega
    simp [this]

lemma validCoefficients_exists (N : Nat) :
    ∃ c : CoefficientData N, ValidCoefficients N c := by
  by_cases hN : N = 0
  · subst N
    exact ⟨_, validCoefficients_zero⟩
  · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    rcases exists_shooting_parameter hNpos with ⟨Ω, hΩ, hres⟩
    exact ⟨shootingData N Ω, shootingData_valid_of_residual hΩ.1 hres⟩

namespace ValidCoefficients

variable {N : Nat} {c : CoefficientData N}

lemma rho_succ_le (v : ValidCoefficients N c) (k : Nat) :
    c.rho (k + 1) ≤ c.rho k := by
  by_cases hk : k ≤ N
  · exact (v.rho_strict k hk).le
  · have htail : N + 1 ≤ k := by omega
    rw [v.rho_tail k htail, v.rho_tail (k + 1) (by omega)]

lemma rho_antitone (v : ValidCoefficients N c) :
    Antitone c.rho :=
  antitone_nat_of_succ_le v.rho_succ_le

lemma rho_pos (v : ValidCoefficients N c) {k : Nat} (hk : k ≤ N) :
    0 < c.rho k := by
  have hnonneg : 0 ≤ c.rho (k + 1) :=
    v.rho_nonneg (k + 1) (Nat.succ_le_succ hk)
  exact lt_of_le_of_lt hnonneg (v.rho_strict k hk)

lemma rho_le_one (v : ValidCoefficients N c) (k : Nat) :
    c.rho k ≤ 1 := by
  have hmono : c.rho k ≤ c.rho 0 := v.rho_antitone (Nat.zero_le k)
  rwa [v.rho_zero] at hmono

lemma last_product (v : ValidCoefficients N c) :
    c.omega * c.rho N = 1 := by
  have hrel := v.recurrence N le_rfl
  have hpos := v.rho_pos (le_rfl : N ≤ N)
  unfold OneStepRel at hrel
  rw [v.rho_terminal] at hrel
  nlinarith

lemma omega_ge_one (v : ValidCoefficients N c) :
    1 ≤ c.omega := by
  calc
    1 = c.omega * c.rho N := v.last_product.symm
    _ ≤ c.omega * 1 :=
      mul_le_mul_of_nonneg_left (v.rho_le_one N) v.omega_pos.le
    _ = c.omega := mul_one _

lemma omega_mul_rho_ge_one
    (v : ValidCoefficients N c) {k : Nat} (hk : k ≤ N) :
    1 ≤ c.omega * c.rho k := by
  have hmono : c.rho N ≤ c.rho k := v.rho_antitone hk
  calc
    1 = c.omega * c.rho N := v.last_product.symm
    _ ≤ c.omega * c.rho k :=
      mul_le_mul_of_nonneg_left hmono v.omega_pos.le

lemma oneStep_domain
    (v : ValidCoefficients N c) {k : Nat} (hk : k ≤ N) :
    OneStepDomain c.omega (c.rho k) :=
  ⟨v.omega_pos, v.rho_pos hk, v.rho_le_one k,
    v.omega_mul_rho_ge_one hk⟩

lemma rho_succ_eq_oneStep
    (v : ValidCoefficients N c) {k : Nat} (hk : k ≤ N) :
    c.rho (k + 1) = oneStep c.omega (c.rho k) := by
  exact oneStep_unique (v.oneStep_domain hk)
    (v.rho_nonneg (k + 1) (Nat.succ_le_succ hk))
    (v.rho_strict k hk) (v.recurrence k hk)

lemma rho_eq_shooting
    (v : ValidCoefficients N c) {k : Nat} (hk : k ≤ N + 1) :
    c.rho k = shooting c.omega k := by
  induction k with
  | zero => exact v.rho_zero
  | succ k ih =>
      have hkN : k ≤ N := by omega
      rw [v.rho_succ_eq_oneStep hkN, shooting_succ, ← ih (by omega)]

end ValidCoefficients

lemma shooting_strictMono_succ_of_valid
    {N k : Nat} {c d : CoefficientData N}
    (vc : ValidCoefficients N c) (vd : ValidCoefficients N d)
    (hΩ : c.omega < d.omega) (hk : k ≤ N) :
    shooting c.omega (k + 1) < shooting d.omega (k + 1) := by
  have hprev : shooting c.omega k ≤ shooting d.omega k := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k ≤ N := by omega
        rw [shooting_succ, shooting_succ]
        have hdomc : OneStepDomain c.omega (shooting c.omega k) := by
          rw [← vc.rho_eq_shooting (by omega)]
          exact vc.oneStep_domain hk'
        have hdomd : OneStepDomain d.omega (shooting d.omega k) := by
          rw [← vd.rho_eq_shooting (by omega)]
          exact vd.oneStep_domain hk'
        have hstrict := oneStep_strictMono_both hΩ (ih hk') hdomc hdomd
        exact hstrict.le
  rw [shooting_succ, shooting_succ]
  have hdomc : OneStepDomain c.omega (shooting c.omega k) := by
    rw [← vc.rho_eq_shooting (by omega)]
    exact vc.oneStep_domain hk
  have hdomd : OneStepDomain d.omega (shooting d.omega k) := by
    rw [← vd.rho_eq_shooting (by omega)]
    exact vd.oneStep_domain hk
  exact oneStep_strictMono_both hΩ hprev hdomc hdomd

lemma validCoefficients_omega_unique
    {N : Nat} {c d : CoefficientData N}
    (vc : ValidCoefficients N c) (vd : ValidCoefficients N d) :
    c.omega = d.omega := by
  rcases lt_trichotomy c.omega d.omega with hlt | heq | hgt
  · have hstrict :=
      shooting_strictMono_succ_of_valid vc vd hlt (le_rfl : N ≤ N)
    rw [← vc.rho_eq_shooting (le_rfl : N + 1 ≤ N + 1),
      ← vd.rho_eq_shooting (le_rfl : N + 1 ≤ N + 1),
      vc.rho_terminal, vd.rho_terminal] at hstrict
    exact (lt_irrefl 0 hstrict).elim
  · exact heq
  · have hstrict :=
      shooting_strictMono_succ_of_valid vd vc hgt (le_rfl : N ≤ N)
    rw [← vd.rho_eq_shooting (le_rfl : N + 1 ≤ N + 1),
      ← vc.rho_eq_shooting (le_rfl : N + 1 ≤ N + 1),
      vd.rho_terminal, vc.rho_terminal] at hstrict
    exact (lt_irrefl 0 hstrict).elim

lemma validCoefficients_unique
    {N : Nat} {c d : CoefficientData N}
    (vc : ValidCoefficients N c) (vd : ValidCoefficients N d) :
    c = d := by
  have hΩ : c.omega = d.omega :=
    validCoefficients_omega_unique vc vd
  have hρ : c.rho = d.rho := by
    funext k
    by_cases hk : k ≤ N + 1
    · calc
        c.rho k = shooting c.omega k := vc.rho_eq_shooting hk
        _ = shooting d.omega k := by rw [hΩ]
        _ = d.rho k := (vd.rho_eq_shooting hk).symm
    · have htail : N + 1 ≤ k := by omega
      rw [vc.rho_tail k htail, vd.rho_tail k htail]
  cases c
  cases d
  simp_all

/-- Existence and uniqueness of the recurrence coefficients for every natural
horizon, including the exact base value `Ω₀ = 1`. -/
theorem recurrence_existsUnique (N : Nat) :
    ∃! c : CoefficientData N, ValidCoefficients N c := by
  rcases validCoefficients_exists N with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact validCoefficients_unique hd hc

/-- The canonical coefficient data selected from the unique existence theorem. -/
noncomputable def canonicalCoefficients (N : Nat) : CoefficientData N :=
  (recurrence_existsUnique N).exists.choose

theorem canonicalCoefficients_valid (N : Nat) :
    ValidCoefficients N (canonicalCoefficients N) :=
  (recurrence_existsUnique N).exists.choose_spec

theorem validCoefficients_eq_canonical
    {N : Nat} {c : CoefficientData N} (hc : ValidCoefficients N c) :
    c = canonicalCoefficients N :=
  (recurrence_existsUnique N).unique hc (canonicalCoefficients_valid N)

/-- The unique recurrence parameter at horizon `N`. -/
noncomputable def omega (N : Nat) : ℝ :=
  (canonicalCoefficients N).omega

/-- The unique recurrence sequence at horizon `N`, extended by zero. -/
noncomputable def rho (N k : Nat) : ℝ :=
  (canonicalCoefficients N).rho k

theorem omega_pos (N : Nat) : 0 < omega N :=
  (canonicalCoefficients_valid N).omega_pos

theorem omega_ge_one (N : Nat) : 1 ≤ omega N :=
  (canonicalCoefficients_valid N).omega_ge_one

@[simp] theorem rho_zero (N : Nat) : rho N 0 = 1 :=
  (canonicalCoefficients_valid N).rho_zero

@[simp] theorem rho_terminal (N : Nat) : rho N (N + 1) = 0 :=
  (canonicalCoefficients_valid N).rho_terminal

theorem rho_nonneg
    (N k : Nat) (hk : k ≤ N + 1) : 0 ≤ rho N k :=
  (canonicalCoefficients_valid N).rho_nonneg k hk

theorem rho_pos
    (N k : Nat) (hk : k ≤ N) : 0 < rho N k :=
  (canonicalCoefficients_valid N).rho_pos hk

theorem rho_le_one (N k : Nat) : rho N k ≤ 1 :=
  (canonicalCoefficients_valid N).rho_le_one k

theorem rho_strict
    (N k : Nat) (hk : k ≤ N) : rho N (k + 1) < rho N k :=
  (canonicalCoefficients_valid N).rho_strict k hk

theorem rho_recurrence
    (N k : Nat) (hk : k ≤ N) :
    OneStepRel (omega N) (rho N k) (rho N (k + 1)) :=
  (canonicalCoefficients_valid N).recurrence k hk

theorem rho_tail
    (N k : Nat) (hk : N + 1 ≤ k) : rho N k = 0 :=
  (canonicalCoefficients_valid N).rho_tail k hk

theorem omega_mul_rho_last (N : Nat) :
    omega N * rho N N = 1 :=
  (canonicalCoefficients_valid N).last_product

theorem omega_mul_rho_ge_one
    (N k : Nat) (hk : k ≤ N) :
    1 ≤ omega N * rho N k :=
  (canonicalCoefficients_valid N).omega_mul_rho_ge_one hk

@[simp] theorem omega_zero : omega 0 = 1 := by
  have hlast := omega_mul_rho_last 0
  rw [rho_zero] at hlast
  simpa using hlast

end LemniAcc
