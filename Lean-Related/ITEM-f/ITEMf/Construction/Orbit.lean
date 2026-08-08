import ITEMf.Construction.TargetAngle

/-!
# The finite backward shooting orbit

The orbit is indexed by the number of backward steps from the terminal angle.
This representation makes the `N = 1` case the zero-step orbit and makes the
comparison proof a direct finite induction.
-/

open Set

set_option autoImplicit false

namespace ITEMf

/-- The angle obtained after `m` backward shooting steps from the terminal
angle. -/
noncomputable def shootingIter (q Upsilon : ℝ) (m : Nat) : ℝ :=
  (oneStep q (candidateP q Upsilon))^[m] (terminalAngle q)

@[simp] lemma shootingIter_zero (q Upsilon : ℝ) :
    shootingIter q Upsilon 0 = terminalAngle q := rfl

@[simp] lemma shootingIter_succ (q Upsilon : ℝ) (m : Nat) :
    shootingIter q Upsilon (m + 1) =
      oneStep q (candidateP q Upsilon) (shootingIter q Upsilon m) := by
  simp [shootingIter, Function.iterate_succ_apply']

lemma shootingFirst_eq_iter (N : Nat) (q Upsilon : ℝ) :
    shootingFirst N q Upsilon = shootingIter q Upsilon (N - 1) := rfl

lemma shootingAngle_eq_iter
    {N : Nat} (q Upsilon : ℝ) (k : Fin N) :
    shootingAngle N q Upsilon k =
      shootingIter q Upsilon (N - 1 - k.1) := rfl

lemma terminalAngle_mem_Ioo
    {q : ℝ} (hq : UnitRatio q) :
    terminalAngle q ∈ Ioo (Real.pi / 2) Real.pi := by
  have hsqrt0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq.1
  have hsqrt1 : Real.sqrt q < 1 := by
    rw [Real.sqrt_lt' zero_lt_one]
    simpa only [one_pow] using hq.2
  have hac0 : 0 < Real.arccos (Real.sqrt q) :=
    Real.arccos_pos.mpr hsqrt1
  have hacHalf : Real.arccos (Real.sqrt q) < Real.pi / 2 :=
    Real.arccos_lt_pi_div_two.mpr hsqrt0
  unfold terminalAngle
  rw [Real.arccos_neg]
  constructor <;> linarith

lemma terminalAngle_cos
    {q : ℝ} (hq : UnitRatio q) :
    Real.cos (terminalAngle q) = -Real.sqrt q := by
  have hsqrt0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hsqrt1 : Real.sqrt q ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hq.2.le
  unfold terminalAngle
  exact Real.cos_arccos (by linarith) (by linarith)

lemma shootingIter_lt_succ
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (m : Nat) :
    shootingIter q Upsilon m < shootingIter q Upsilon (m + 1) := by
  rw [shootingIter_succ]
  have hinc :=
    oneStep_increment_mem_Ioo hq
      (candidateP_pos hq hUpsilon)
      (candidateP_lt_q hq hUpsilon)
      (shootingIter q Upsilon m)
  linarith [hinc.1]

lemma shootingIter_strictMono
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    StrictMono (shootingIter q Upsilon) :=
  strictMono_nat_of_lt_succ (shootingIter_lt_succ hq hUpsilon)

lemma shootingIter_le_first
    {N : Nat} {q Upsilon : ℝ}
    (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    {m : Nat} (hm : m ≤ N - 1) :
    shootingIter q Upsilon m ≤ shootingFirst N q Upsilon := by
  rw [shootingFirst_eq_iter]
  exact (shootingIter_strictMono hq hUpsilon).monotone hm

lemma shootingIter_gt_pi_div_two
    {q Upsilon : ℝ}
    (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) (m : Nat) :
    Real.pi / 2 < shootingIter q Upsilon m := by
  have hbase := (terminalAngle_mem_Ioo hq).1
  have hmono :
      terminalAngle q ≤ shootingIter q Upsilon m := by
    simpa only [shootingIter_zero] using
      (shootingIter_strictMono hq hUpsilon).monotone (Nat.zero_le m)
  exact hbase.trans_le hmono

lemma shootingIter_cos_neg_of_first_le_pi
    {N : Nat} {q Upsilon : ℝ}
    (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hfirst : shootingFirst N q Upsilon ≤ Real.pi)
    {m : Nat} (hm : m ≤ N - 1) :
    Real.cos (shootingIter q Upsilon m) < 0 := by
  have hlower := shootingIter_gt_pi_div_two hq hUpsilon m
  have hupper :
      shootingIter q Upsilon m < Real.pi + Real.pi / 2 := by
    have hle := shootingIter_le_first hq hUpsilon hm
    have hhalf : 0 < Real.pi / 2 := by positivity
    linarith
  exact Real.cos_neg_of_pi_div_two_lt_of_lt hlower hupper

lemma shootingIter_comparison
    {N m : Nat} {q Upsilon Upsilon' : ℝ}
    (hq : UnitRatio q)
    (hUpsilon : 1 < Upsilon) (hUpsilon' : 1 < Upsilon')
    (horder : Upsilon < Upsilon')
    (hfirst : shootingFirst N q Upsilon ≤ Real.pi)
    (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) :
    shootingIter q Upsilon' m < shootingIter q Upsilon m := by
  have hp :
      candidateP q Upsilon < candidateP q Upsilon' :=
    candidateP_strictMonoOn hq hUpsilon hUpsilon' horder
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm0
  induction j with
  | zero =>
      simp only [Nat.zero_add, shootingIter_succ, shootingIter_zero]
      exact oneStep_parameter_decreases hq
        (candidateP_pos hq hUpsilon)
        (candidateP_lt_q hq hUpsilon)
        (candidateP_pos hq hUpsilon')
        (candidateP_lt_q hq hUpsilon')
        hp
        (by
          rw [terminalAngle_cos hq]
          exact neg_neg_of_pos (Real.sqrt_pos.2 hq.1))
  | succ j ih =>
      have hjN : j + 1 ≤ N - 1 := by omega
      have hjN' : 1 + j ≤ N - 1 := by omega
      have ih' := ih (by omega) hjN'
      rw [show 1 + (j + 1) = (1 + j) + 1 by omega,
        shootingIter_succ, shootingIter_succ]
      have hangle :=
        oneStep_strictMono hq
          (candidateP_pos hq hUpsilon')
          (candidateP_lt_q hq hUpsilon') ih'
      have hparam :=
        oneStep_parameter_decreases hq
          (candidateP_pos hq hUpsilon)
          (candidateP_lt_q hq hUpsilon)
          (candidateP_pos hq hUpsilon')
          (candidateP_lt_q hq hUpsilon')
          hp
          (shootingIter_cos_neg_of_first_le_pi
            (m := 1 + j) hq hUpsilon hfirst hjN')
      exact hangle.trans hparam

namespace Internal

/-- Strict comparison of every nonterminal angle in two finite shooting
orbits. -/
theorem orbitComparison
    (N : Nat) (q Upsilon Upsilon' : ℝ)
    (hN : 2 ≤ N) (hq : UnitRatio q)
    (hUpsilon : 1 < Upsilon) (horder : Upsilon < Upsilon')
    (hfirst : shootingFirst N q Upsilon ≤ Real.pi) :
    OrbitComparisonResult N q Upsilon Upsilon' := by
  have hUpsilon' : 1 < Upsilon' := hUpsilon.trans horder
  intro k
  have hk : k.1 < N - 1 := k.2
  change
    shootingIter q Upsilon' (N - 1 - k.1) <
      shootingIter q Upsilon (N - 1 - k.1)
  apply shootingIter_comparison hq hUpsilon hUpsilon' horder hfirst
  · omega
  · omega

end Internal
end ITEMf
