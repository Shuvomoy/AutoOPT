import ITEMf.Construction.ShootingSufficient

/-!
# Continuity and endpoint signs of the shooting residual

The parameterized finite orbit isolates the two boundary parameters `p = 0`
and `p = q`; no strict-domain one-step theorem is applied at either endpoint.
-/

open Set Filter

set_option autoImplicit false

namespace ITEMf

/-- The finite backward orbit with the step parameter exposed. -/
noncomputable def parameterIter (q p : ℝ) (m : Nat) : ℝ :=
  (oneStep q p)^[m] (terminalAngle q)

@[simp] lemma parameterIter_zero (q p : ℝ) :
    parameterIter q p 0 = terminalAngle q := rfl

@[simp] lemma parameterIter_succ (q p : ℝ) (m : Nat) :
    parameterIter q p (m + 1) =
      oneStep q p (parameterIter q p m) := by
  simp [parameterIter, Function.iterate_succ_apply']

lemma shootingIter_eq_parameterIter
    (q Upsilon : ℝ) (m : Nat) :
    shootingIter q Upsilon m =
      parameterIter q (candidateP q Upsilon) m := rfl

lemma parameterIter_continuous (q : ℝ) (m : Nat) :
    Continuous (fun p : ℝ => parameterIter q p m) := by
  induction m with
  | zero =>
      simp only [parameterIter_zero]
      fun_prop
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega]
      simp only [Nat.succ_eq_add_one, parameterIter_succ]
      unfold oneStep oneStepArg
      fun_prop

lemma shootingFirst_continuousOn
    {N : Nat} {q : ℝ} (hq : UnitRatio q) :
    ContinuousOn (shootingFirst N q) (Ioi (1 : ℝ)) := by
  rw [show shootingFirst N q =
      fun Upsilon =>
        parameterIter q (candidateP q Upsilon) (N - 1) by
    funext Upsilon
    rfl]
  exact (parameterIter_continuous q (N - 1)).continuousOn.comp
    (candidateP_continuousOn q)
    (fun _ _ => Set.mem_univ _)

lemma shootingResidual_continuousOn
    {N : Nat} {q : ℝ} (hq : UnitRatio q) :
    ContinuousOn (shootingResidual N q) (Ioi (1 : ℝ)) := by
  unfold shootingResidual
  exact (shootingFirst_continuousOn hq).sub
    (targetAngle_continuousOn hq)

lemma parameterIter_zero_parameter
    (q : ℝ) (m : Nat) :
    parameterIter q 0 m =
      terminalAngle q + m * Real.arccos (1 - q) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [parameterIter_succ, ih]
      unfold oneStep oneStepArg
      push_cast
      ring

lemma shootingFirst_tendsto_one
    {N : Nat} {q : ℝ} (hq : UnitRatio q) :
    Tendsto (shootingFirst N q) (nhdsWithin (1 : ℝ) (Ioi 1))
      (nhds
        (terminalAngle q +
          ((N - 1 : Nat) : ℝ) * Real.arccos (1 - q))) := by
  have hp := candidateP_tendsto_one (q := q)
  have hcont :=
    (parameterIter_continuous q (N - 1)).tendsto 0
  have hcomp := hcont.comp hp
  rw [parameterIter_zero_parameter] at hcomp
  change
    Tendsto
      (fun Upsilon =>
        parameterIter q (candidateP q Upsilon) (N - 1))
      (nhdsWithin (1 : ℝ) (Ioi 1))
      (nhds
        (terminalAngle q +
          ((N - 1 : Nat) : ℝ) * Real.arccos (1 - q)))
  exact hcomp

lemma boundaryOneStep_mem_Ioo
    {q theta : ℝ} (hq : UnitRatio q)
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    oneStep q q theta ∈ Ioo (0 : ℝ) Real.pi := by
  have hcosLower : -1 < Real.cos theta := by
    rw [← Real.cos_pi]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      htheta.1.le le_rfl htheta.2
  have hcosUpper : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have hargLower :
      -1 < oneStepArg q q theta := by
    unfold oneStepArg
    nlinarith [hq.1, hq.2]
  have hargUpper :
      oneStepArg q q theta < 1 := by
    unfold oneStepArg
    nlinarith [mul_pos hq.1 (by linarith : 0 < 1 + Real.cos theta)]
  have hminusCosLower : -1 ≤ -Real.cos theta := by linarith
  have hminusCosUpper : -Real.cos theta ≤ 1 := by
    linarith [Real.neg_one_le_cos theta]
  have hargCompare :
      -Real.cos theta < oneStepArg q q theta := by
    unfold oneStepArg
    nlinarith [mul_pos (by linarith [hq.2] : 0 < 1 - q)
      (by linarith : 0 < 1 + Real.cos theta)]
  have harccos :
      Real.arccos (oneStepArg q q theta) <
        Real.arccos (-Real.cos theta) :=
    Real.arccos_lt_arccos hminusCosLower hargCompare hargUpper.le
  have hthetaArccos :
      Real.arccos (-Real.cos theta) = Real.pi - theta := by
    rw [Real.arccos_neg, Real.arccos_cos htheta.1.le htheta.2.le]
  have hstepPos :
      0 < Real.arccos (oneStepArg q q theta) :=
    Real.arccos_pos.mpr hargUpper
  have hthetaPos := htheta.1
  unfold oneStep
  rw [hthetaArccos] at harccos
  constructor <;> linarith

lemma parameterIter_boundary_mem_Ioo
    {q : ℝ} (hq : UnitRatio q) (m : Nat) :
    parameterIter q q m ∈ Ioo (0 : ℝ) Real.pi := by
  induction m with
  | zero =>
      have hterminal := terminalAngle_mem_Ioo hq
      simpa only [parameterIter_zero] using
        (show terminalAngle q ∈ Ioo (0 : ℝ) Real.pi by
          constructor
          · have hpi : 0 < Real.pi / 2 := by positivity
            have hlower := hterminal.1
            linarith
          · exact hterminal.2)
  | succ m ih =>
      rw [parameterIter_succ]
      exact boundaryOneStep_mem_Ioo hq ih

lemma shootingFirst_tendsto_atTop
    {N : Nat} {q : ℝ} (hq : UnitRatio q) :
    Tendsto (shootingFirst N q) atTop
      (nhds (parameterIter q q (N - 1))) := by
  have hp := candidateP_tendsto_atTop (q := q)
  have hcont :=
    (parameterIter_continuous q (N - 1)).tendsto q
  change
    Tendsto
      (fun Upsilon =>
        parameterIter q (candidateP q Upsilon) (N - 1))
      atTop (nhds (parameterIter q q (N - 1)))
  exact hcont.comp hp

lemma shootingResidual_tendsto_one
    {N : Nat} {q : ℝ} (hq : UnitRatio q) :
    Tendsto (shootingResidual N q) (nhdsWithin (1 : ℝ) (Ioi 1))
      (nhds
        (terminalAngle q +
          ((N - 1 : Nat) : ℝ) * Real.arccos (1 - q) -
          Real.arccos (Real.sqrt q))) := by
  unfold shootingResidual
  exact (shootingFirst_tendsto_one hq).sub
    (targetAngle_tendsto_one hq)

lemma shootingResidual_tendsto_atTop
    {N : Nat} {q : ℝ} (hq : UnitRatio q) :
    Tendsto (shootingResidual N q) atTop
      (nhds (parameterIter q q (N - 1) - Real.pi)) := by
  unfold shootingResidual
  exact (shootingFirst_tendsto_atTop hq).sub
    (targetAngle_tendsto_atTop hq)

lemma residual_one_limit_pos
    {N : Nat} {q : ℝ} (hN : 1 ≤ N) (hq : UnitRatio q) :
    0 <
      terminalAngle q +
        ((N - 1 : Nat) : ℝ) * Real.arccos (1 - q) -
        Real.arccos (Real.sqrt q) := by
  have hsqrtPos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq.1
  have hacLt :
      Real.arccos (Real.sqrt q) < Real.pi / 2 :=
    Real.arccos_lt_pi_div_two.mpr hsqrtPos
  have hterm :
      terminalAngle q =
        Real.pi - Real.arccos (Real.sqrt q) := by
    unfold terminalAngle
    rw [Real.arccos_neg]
  have hnonneg :
      0 ≤ ((N - 1 : Nat) : ℝ) * Real.arccos (1 - q) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.arccos_nonneg _)
  rw [hterm]
  linarith

lemma residual_atTop_limit_neg
    {N : Nat} {q : ℝ} (hq : UnitRatio q) :
    parameterIter q q (N - 1) - Real.pi < 0 := by
  have hmem := parameterIter_boundary_mem_Ioo hq (N - 1)
  have hupper := hmem.2
  linarith

lemma exists_residual_pos
    {N : Nat} {q : ℝ} (hN : 1 ≤ N) (hq : UnitRatio q) :
    ∃ Upsilon : ℝ,
      1 < Upsilon ∧ 0 < shootingResidual N q Upsilon := by
  have heventually :
      ∀ᶠ Upsilon in nhdsWithin (1 : ℝ) (Ioi 1),
        0 < shootingResidual N q Upsilon :=
    tendsto_const_nhds.eventually_lt
      (shootingResidual_tendsto_one hq)
      (residual_one_limit_pos hN hq)
  have hdomain :
      ∀ᶠ Upsilon in nhdsWithin (1 : ℝ) (Ioi 1),
        Upsilon ∈ Ioi (1 : ℝ) :=
    self_mem_nhdsWithin
  rcases (hdomain.and heventually).exists with
    ⟨Upsilon, hUpsilon, hpositive⟩
  exact ⟨Upsilon, hUpsilon, hpositive⟩

lemma exists_residual_neg_above
    {N : Nat} {q A : ℝ} (hq : UnitRatio q) :
    ∃ Upsilon : ℝ,
      A < Upsilon ∧ shootingResidual N q Upsilon < 0 := by
  have heventually :
      ∀ᶠ Upsilon in atTop, shootingResidual N q Upsilon < 0 :=
    (shootingResidual_tendsto_atTop hq).eventually_lt
      tendsto_const_nhds (residual_atTop_limit_neg hq)
  rcases ((eventually_gt_atTop A).and heventually).exists with
    ⟨Upsilon, hA, hnegative⟩
  exact ⟨Upsilon, hA, hnegative⟩

lemma exists_residual_root
    {N : Nat} {q : ℝ} (hN : 1 ≤ N) (hq : UnitRatio q) :
    ∃ Upsilon : ℝ,
      1 < Upsilon ∧ shootingResidual N q Upsilon = 0 := by
  rcases exists_residual_pos hN hq with
    ⟨a, haOne, haPositive⟩
  rcases exists_residual_neg_above (N := N) (A := a) hq with
    ⟨b, hab, hbNegative⟩
  have hcontinuous :
      ContinuousOn (shootingResidual N q) (Icc a b) :=
    (shootingResidual_continuousOn hq).mono (by
      intro U hU
      exact haOne.trans_le hU.1)
  have hzero :
      (0 : ℝ) ∈
        Icc (shootingResidual N q b) (shootingResidual N q a) :=
    ⟨hbNegative.le, haPositive.le⟩
  rcases
      (intermediate_value_Icc' hab.le hcontinuous hzero) with
    ⟨Upsilon, hUpsilon, hroot⟩
  exact ⟨Upsilon, haOne.trans_le hUpsilon.1, hroot⟩

lemma residual_root_unique
    {N : Nat} {q Upsilon Upsilon' : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hUpsilon : 1 < Upsilon) (hUpsilon' : 1 < Upsilon')
    (hroot : shootingResidual N q Upsilon = 0)
    (hroot' : shootingResidual N q Upsilon' = 0) :
    Upsilon = Upsilon' := by
  apply le_antisymm
  · by_contra hnot
    have horder : Upsilon' < Upsilon := lt_of_not_ge hnot
    have hclose :
        shootingFirst N q Upsilon =
          targetAngleValue q Upsilon :=
      shootingFirst_eq_target_of_residual hroot
    have hclose' :
        shootingFirst N q Upsilon' =
          targetAngleValue q Upsilon' :=
      shootingFirst_eq_target_of_residual hroot'
    have htarget :
        targetAngleValue q Upsilon' <
          targetAngleValue q Upsilon :=
      targetAngle_strictMonoOn hq hUpsilon' hUpsilon horder
    by_cases hN1 : N = 1
    · subst N
      have hfirst :
          shootingFirst 1 q Upsilon =
            shootingFirst 1 q Upsilon' := by
        rfl
      linarith
    · have hN2 : 2 ≤ N := by omega
      have hfirstLe :
          shootingFirst N q Upsilon' ≤ Real.pi := by
        rw [hclose']
        exact (targetAngle_range hq hUpsilon').2.le
      have hcompare :
          shootingFirst N q Upsilon <
            shootingFirst N q Upsilon' := by
        rw [shootingFirst_eq_iter, shootingFirst_eq_iter]
        exact shootingIter_comparison hq hUpsilon' hUpsilon horder
          hfirstLe (by omega) le_rfl
      linarith
  · by_contra hnot
    have horder : Upsilon < Upsilon' := lt_of_not_ge hnot
    have hclose :
        shootingFirst N q Upsilon =
          targetAngleValue q Upsilon :=
      shootingFirst_eq_target_of_residual hroot
    have hclose' :
        shootingFirst N q Upsilon' =
          targetAngleValue q Upsilon' :=
      shootingFirst_eq_target_of_residual hroot'
    have htarget :
        targetAngleValue q Upsilon <
          targetAngleValue q Upsilon' :=
      targetAngle_strictMonoOn hq hUpsilon hUpsilon' horder
    by_cases hN1 : N = 1
    · subst N
      have hfirst :
          shootingFirst 1 q Upsilon =
            shootingFirst 1 q Upsilon' := by
        rfl
      linarith
    · have hN2 : 2 ≤ N := by omega
      have hfirstLe :
          shootingFirst N q Upsilon ≤ Real.pi := by
        rw [hclose]
        exact (targetAngle_range hq hUpsilon).2.le
      have hcompare :
          shootingFirst N q Upsilon' <
            shootingFirst N q Upsilon := by
        rw [shootingFirst_eq_iter, shootingFirst_eq_iter]
        exact shootingIter_comparison hq hUpsilon hUpsilon' horder
          hfirstLe (by omega) le_rfl
      linarith

theorem existsUnique_residual_root
    {N : Nat} {q : ℝ} (hN : 1 ≤ N) (hq : UnitRatio q) :
    ∃! Upsilon : ℝ,
      1 < Upsilon ∧ shootingResidual N q Upsilon = 0 := by
  rcases exists_residual_root hN hq with
    ⟨Upsilon, hUpsilon, hroot⟩
  refine ⟨Upsilon, ⟨hUpsilon, hroot⟩, ?_⟩
  intro Upsilon' hUpsilon'
  exact residual_root_unique hN hq
    hUpsilon'.1 hUpsilon hUpsilon'.2 hroot

end ITEMf
