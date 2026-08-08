import ITEMf.Construction.Geometry

/-!
# Sufficiency of the ITEM-f shooting equation

This module constructs the unique candidate point table from a zero of the
shooting residual and verifies every finite ordering, circle, and chord
condition.
-/

open Set

set_option autoImplicit false

namespace ITEMf

lemma terminalAngle_sin
    {q : ℝ} (hq : UnitRatio q) :
    Real.sin (terminalAngle q) = Real.sqrt (1 - q) := by
  have hq0 : 0 ≤ q := hq.1.le
  have hq1 : 0 ≤ 1 - q := by linarith [hq.2]
  have hsqrtqSq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  unfold terminalAngle
  rw [Real.sin_arccos]
  congr 1
  nlinarith

lemma shootingFirst_eq_target_of_residual
    {N : Nat} {q Upsilon : ℝ}
    (hres : shootingResidual N q Upsilon = 0) :
    shootingFirst N q Upsilon = targetAngleValue q Upsilon := by
  unfold shootingResidual at hres
  linarith

lemma shootingAngle_mem_Ioo_of_residual
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hres : shootingResidual N q Upsilon = 0) (k : Fin N) :
    shootingAngle N q Upsilon k ∈ Ioo (0 : ℝ) Real.pi := by
  have hm : N - 1 - k.1 ≤ N - 1 := Nat.sub_le _ _
  have hlower :
      Real.pi / 2 <
        shootingIter q Upsilon (N - 1 - k.1) :=
    shootingIter_gt_pi_div_two hq hUpsilon _
  have hle :
      shootingIter q Upsilon (N - 1 - k.1) ≤
        shootingFirst N q Upsilon :=
    shootingIter_le_first hq hUpsilon hm
  have htarget :=
    targetAngle_range hq hUpsilon
  have hclose := shootingFirst_eq_target_of_residual hres
  rw [shootingAngle_eq_iter]
  constructor
  · have hpi : 0 < Real.pi / 2 := by positivity
    linarith
  · rw [hclose] at hle
    exact hle.trans_lt htarget.2

lemma shootingAngle_gt_pi_div_two
    {N : Nat} {q Upsilon : ℝ}
    (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) (k : Fin N) :
    Real.pi / 2 < shootingAngle N q Upsilon k := by
  rw [shootingAngle_eq_iter]
  exact shootingIter_gt_pi_div_two hq hUpsilon _

lemma shootingAngle_strictAnti
    {N : Nat} {q Upsilon : ℝ}
    (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    {i j : Fin N} (hij : i.1 < j.1) :
    shootingAngle N q Upsilon j < shootingAngle N q Upsilon i := by
  rw [shootingAngle_eq_iter, shootingAngle_eq_iter]
  apply shootingIter_strictMono hq hUpsilon
  omega

lemma shootingAngle_step
    {N : Nat} {q Upsilon : ℝ} (k : Fin (N - 1)) :
    shootingAngle N q Upsilon ⟨k.1, by omega⟩ =
      oneStep q (candidateP q Upsilon)
        (shootingAngle N q Upsilon ⟨k.1 + 1, by omega⟩) := by
  rw [shootingAngle_eq_iter, shootingAngle_eq_iter]
  have hexp :
      N - 1 - k.1 = (N - 1 - (k.1 + 1)) + 1 := by omega
  rw [hexp, shootingIter_succ]

lemma shootingFirst_eq_firstAngle
    {N : Nat} (hN : 1 ≤ N) (q Upsilon : ℝ) :
    shootingFirst N q Upsilon =
      shootingAngle N q Upsilon ⟨0, by omega⟩ := by
  rw [shootingFirst_eq_iter, shootingAngle_eq_iter]
  simp only [Fin.val_mk, Nat.sub_zero]

lemma candidateA_interior_strict
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hres : shootingResidual N q Upsilon = 0)
    {i j : Fin N} (hij : i.1 < j.1) :
    candidateA N q Upsilon (idxInterior i) <
      candidateA N q Upsilon (idxInterior j) := by
  rw [candidateA_interior, candidateA_interior]
  have hi := shootingAngle_mem_Ioo_of_residual hN hq hUpsilon hres i
  have hj := shootingAngle_mem_Ioo_of_residual hN hq hUpsilon hres j
  have hangle := shootingAngle_strictAnti hq hUpsilon hij
  have hcos :
      Real.cos (shootingAngle N q Upsilon i) <
        Real.cos (shootingAngle N q Upsilon j) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · exact hj.1.le
    · exact hi.2.le
    · exact hangle
  simpa only [add_comm] using
    add_lt_add_left
      (mul_lt_mul_of_pos_left hcos (radius_pos hUpsilon)) Upsilon

lemma candidateA_zero_lt_interior
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hres : shootingResidual N q Upsilon = 0) (k : Fin N) :
    candidateA N q Upsilon (idxZero N) <
      candidateA N q Upsilon (idxInterior k) := by
  rw [candidateA_zero, candidateA_interior]
  let first : Fin N := ⟨0, by omega⟩
  have hk := shootingAngle_mem_Ioo_of_residual hN hq hUpsilon hres k
  have hfirst :=
    shootingAngle_mem_Ioo_of_residual hN hq hUpsilon hres first
  have hm :
      N - 1 - k.1 ≤ N - 1 := Nat.sub_le _ _
  have hangle :
      shootingAngle N q Upsilon k ≤
        shootingAngle N q Upsilon first := by
    rw [shootingAngle_eq_iter, shootingAngle_eq_iter]
    exact (shootingIter_strictMono hq hUpsilon).monotone (by
      simpa only [first, Nat.sub_zero] using hm)
  have hcos :
      Real.cos (shootingAngle N q Upsilon first) ≤
        Real.cos (shootingAngle N q Upsilon k) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      hk.1.le hfirst.2.le hangle
  have htarget :
      1 / Upsilon <
        Upsilon +
          radius Upsilon * Real.cos (shootingAngle N q Upsilon first) := by
    rw [← shootingFirst_eq_firstAngle hN q Upsilon,
      shootingFirst_eq_target_of_residual hres]
    exact inv_lt_targetAbscissa hq hUpsilon
  have hR := radius_pos hUpsilon
  nlinarith

lemma candidateA_interior_lt_last
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hres : shootingResidual N q Upsilon = 0) (k : Fin N) :
    candidateA N q Upsilon (idxInterior k) <
      candidateA N q Upsilon (idxLast N) := by
  rw [candidateA_interior, candidateA_last]
  have hk := shootingAngle_mem_Ioo_of_residual hN hq hUpsilon hres k
  have hhalf := shootingAngle_gt_pi_div_two hq hUpsilon k
  have hcos :
      Real.cos (shootingAngle N q Upsilon k) < 0 := by
    rw [← Real.cos_pi_div_two]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (by positivity) hk.2.le hhalf
  nlinarith [radius_pos hUpsilon]

lemma candidateA_strict
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hres : shootingResidual N q Upsilon = 0)
    {i j : Fin (N + 2)} (hij : i.1 < j.1) :
    candidateA N q Upsilon i < candidateA N q Upsilon j := by
  by_cases hi0 : i.1 = 0
  · have hi : i = idxZero N := Fin.ext hi0
    subst i
    by_cases hjlast : j.1 = N + 1
    · have hj : j = idxLast N := Fin.ext hjlast
      rw [hj]
      rw [candidateA_zero, candidateA_last]
      have hU : 0 < Upsilon := zero_lt_one.trans hUpsilon
      rw [div_lt_iff₀ hU]
      nlinarith [mul_pos (sub_pos.mpr hUpsilon)
        (add_pos hU zero_lt_one)]
    · let jk : Fin N := ⟨j.1 - 1, by omega⟩
      have hj : j = idxInterior jk := by
        apply Fin.ext
        simp only [idxInterior, jk]
        omega
      rw [hj]
      exact candidateA_zero_lt_interior hN hq hUpsilon hres jk
  · by_cases hjlast : j.1 = N + 1
    · have hj : j = idxLast N := Fin.ext hjlast
      subst j
      let ik : Fin N := ⟨i.1 - 1, by omega⟩
      have hi : i = idxInterior ik := by
        apply Fin.ext
        simp only [idxInterior, ik]
        omega
      rw [hi]
      exact candidateA_interior_lt_last hN hq hUpsilon hres ik
    · let ik : Fin N := ⟨i.1 - 1, by omega⟩
      let jk : Fin N := ⟨j.1 - 1, by omega⟩
      have hi : i = idxInterior ik := by
        apply Fin.ext
        simp only [idxInterior, ik]
        omega
      have hj : j = idxInterior jk := by
        apply Fin.ext
        simp only [idxInterior, jk]
        omega
      rw [hi, hj]
      apply candidateA_interior_strict hN hq hUpsilon hres
      simp only [ik, jk]
      omega

lemma candidateB_pos
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hres : shootingResidual N q Upsilon = 0)
    (i : Fin (N + 2)) :
    0 < candidateB N q Upsilon i := by
  by_cases hi0 : i.1 = 0
  · have hi : i = idxZero N := Fin.ext hi0
    subst i
    rw [candidateB_zero]
    exact div_pos
      (mul_pos (Real.sqrt_pos.2 (by linarith [hq.2]))
        (radius_pos hUpsilon))
      (zero_lt_one.trans hUpsilon)
  · by_cases hilast : i.1 = N + 1
    · have hi : i = idxLast N := Fin.ext hilast
      subst i
      rw [candidateB_last]
      exact mul_pos (Real.sqrt_pos.2 (by linarith [hq.2]))
        (radius_pos hUpsilon)
    · let k : Fin N := ⟨i.1 - 1, by omega⟩
      have hi : i = idxInterior k := by
        apply Fin.ext
        simp only [idxInterior, k]
        omega
      rw [hi]
      rw [candidateB_interior]
      exact mul_pos (radius_pos hUpsilon)
        (Real.sin_pos_of_pos_of_lt_pi
          (shootingAngle_mem_Ioo_of_residual
            hN hq hUpsilon hres k).1
          (shootingAngle_mem_Ioo_of_residual
            hN hq hUpsilon hres k).2)

lemma candidate_circle
    {N : Nat} {q Upsilon : ℝ}
    (hUpsilon : 1 < Upsilon) (k : Fin N) :
    (candidateA N q Upsilon (idxInterior k) - Upsilon) ^ 2 +
          candidateB N q Upsilon (idxInterior k) ^ 2 =
      radiusSq Upsilon := by
  rw [candidateA_interior, candidateB_interior]
  have htrig :=
    Real.sin_sq_add_cos_sq (shootingAngle N q Upsilon k)
  have hR2 := radius_sq hUpsilon
  rw [← hR2]
  calc
    (Upsilon +
          radius Upsilon * Real.cos (shootingAngle N q Upsilon k) -
        Upsilon) ^ 2 +
        (radius Upsilon *
          Real.sin (shootingAngle N q Upsilon k)) ^ 2 =
      radius Upsilon ^ 2 *
        (Real.sin (shootingAngle N q Upsilon k) ^ 2 +
          Real.cos (shootingAngle N q Upsilon k) ^ 2) := by ring
    _ = radius Upsilon ^ 2 := by rw [htrig, mul_one]

lemma candidate_chord_zero
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hres : shootingResidual N q Upsilon = 0) :
    let first : Fin N := ⟨0, by omega⟩
    (candidateA N q Upsilon (idxZero N) - Upsilon) *
          (candidateA N q Upsilon (idxInterior first) - Upsilon) +
        candidateB N q Upsilon (idxZero N) *
          candidateB N q Upsilon (idxInterior first) =
      radiusSq Upsilon *
        (1 - q * candidateA N q Upsilon (idxInterior first) / Upsilon) := by
  dsimp only
  rw [candidateA_zero, candidateB_zero,
    candidateA_interior, candidateB_interior]
  have hU : 0 < Upsilon := zero_lt_one.trans hUpsilon
  have hUne : Upsilon ≠ 0 := ne_of_gt hU
  have hangle :
      shootingAngle N q Upsilon ⟨0, by omega⟩ =
        targetAngleValue q Upsilon := by
    rw [← shootingFirst_eq_firstAngle hN q Upsilon,
      shootingFirst_eq_target_of_residual hres]
  have hline :
      Real.sin (shootingAngle N q Upsilon ⟨0, by omega⟩) =
        Real.sqrt (1 - q) *
          (Upsilon + radius Upsilon *
            Real.cos (shootingAngle N q Upsilon ⟨0, by omega⟩)) := by
    rw [hangle]
    exact targetAngle_line hq hUpsilon
  have hs2 :
      Real.sqrt (1 - q) ^ 2 = 1 - q :=
    Real.sq_sqrt (by linarith [hq.2])
  have hR2 : radius Upsilon ^ 2 = Upsilon ^ 2 - 1 := by
    simpa [radiusSq] using radius_sq hUpsilon
  rw [hline]
  unfold radiusSq
  field_simp [hUne]
  ring_nf
  rw [hs2]
  linear_combination
    (Upsilon * (1 - q) -
      q * radius Upsilon *
        Real.cos (shootingAngle N q Upsilon ⟨0, by omega⟩) +
      radius Upsilon *
        Real.cos (shootingAngle N q Upsilon ⟨0, by omega⟩)) * hR2

lemma candidate_chord_terminal
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    let lastInterior : Fin N := ⟨N - 1, by omega⟩
    (candidateA N q Upsilon (idxInterior lastInterior) - Upsilon) *
          (candidateA N q Upsilon (idxLast N) - Upsilon) +
        candidateB N q Upsilon (idxInterior lastInterior) *
          candidateB N q Upsilon (idxLast N) =
      radiusSq Upsilon *
        (1 - q * candidateA N q Upsilon (idxLast N) / Upsilon) := by
  dsimp only
  rw [candidateA_interior, candidateB_interior,
    candidateA_last, candidateB_last]
  have hangle :
      shootingAngle N q Upsilon ⟨N - 1, by omega⟩ =
        terminalAngle q := by
    rw [shootingAngle_eq_iter]
    have hexp : N - 1 - (N - 1) = 0 := by omega
    rw [hexp, shootingIter_zero]
  rw [hangle, terminalAngle_cos hq, terminalAngle_sin hq]
  have hUne : Upsilon ≠ 0 :=
    ne_of_gt (zero_lt_one.trans hUpsilon)
  have hs2 :
      Real.sqrt (1 - q) ^ 2 = 1 - q :=
    Real.sq_sqrt (by linarith [hq.2])
  rw [← radius_sq hUpsilon]
  field_simp [hUne]
  ring_nf
  rw [hs2]
  ring

lemma candidate_chord_interior
    {N : Nat} {q Upsilon : ℝ}
    (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (k : Fin (N - 1)) :
    let left : Fin N := ⟨k.1, by omega⟩
    let right : Fin N := ⟨k.1 + 1, by omega⟩
    (candidateA N q Upsilon (idxInterior left) - Upsilon) *
          (candidateA N q Upsilon (idxInterior right) - Upsilon) +
        candidateB N q Upsilon (idxInterior left) *
          candidateB N q Upsilon (idxInterior right) =
      radiusSq Upsilon *
        (1 - q * candidateA N q Upsilon (idxInterior right) / Upsilon) := by
  dsimp only
  rw [candidateA_interior, candidateA_interior,
    candidateB_interior, candidateB_interior]
  let thetaL :=
    shootingAngle N q Upsilon ⟨k.1, by omega⟩
  let thetaR :=
    shootingAngle N q Upsilon ⟨k.1 + 1, by omega⟩
  have hstep :
      thetaL = oneStep q (candidateP q Upsilon) thetaR := by
    simpa only [thetaL, thetaR] using shootingAngle_step k
  have hp0 := candidateP_pos hq hUpsilon
  have hpq := candidateP_lt_q hq hUpsilon
  have harg :=
    oneStepArg_mem_Ioo hq hp0 hpq thetaR
  have hcosDiff :
      Real.cos (thetaL - thetaR) =
        oneStepArg q (candidateP q Upsilon) thetaR := by
    rw [hstep]
    unfold oneStep
    simp only [add_sub_cancel_left]
    exact Real.cos_arccos harg.1.le harg.2.le
  change
    (Upsilon + radius Upsilon * Real.cos thetaL - Upsilon) *
          (Upsilon + radius Upsilon * Real.cos thetaR - Upsilon) +
        radius Upsilon * Real.sin thetaL *
          (radius Upsilon * Real.sin thetaR) =
      radiusSq Upsilon *
        (1 -
          q * (Upsilon + radius Upsilon * Real.cos thetaR) / Upsilon)
  have hUne : Upsilon ≠ 0 :=
    ne_of_gt (zero_lt_one.trans hUpsilon)
  rw [← radius_sq hUpsilon]
  calc
    (Upsilon + radius Upsilon * Real.cos thetaL - Upsilon) *
            (Upsilon + radius Upsilon * Real.cos thetaR - Upsilon) +
          radius Upsilon * Real.sin thetaL *
            (radius Upsilon * Real.sin thetaR) =
        radius Upsilon ^ 2 * Real.cos (thetaL - thetaR) := by
      rw [Real.cos_sub]
      ring
    _ = radius Upsilon ^ 2 *
        oneStepArg q (candidateP q Upsilon) thetaR := by rw [hcosDiff]
    _ = radius Upsilon ^ 2 *
        (1 -
          q * (Upsilon + radius Upsilon * Real.cos thetaR) / Upsilon) := by
      rw [candidateP_eq_q_mul_radius_div hUpsilon]
      unfold oneStepArg
      field_simp [hUne]
      ring

lemma candidate_chord
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hres : shootingResidual N q Upsilon = 0)
    (k : Fin (N + 1)) :
    (candidateA N q Upsilon (idxChordLeft k) - Upsilon) *
          (candidateA N q Upsilon (idxChordRight k) - Upsilon) +
        candidateB N q Upsilon (idxChordLeft k) *
          candidateB N q Upsilon (idxChordRight k) =
      radiusSq Upsilon *
        (1 - q * candidateA N q Upsilon (idxChordRight k) / Upsilon) := by
  by_cases hk0 : k.1 = 0
  · have hleft : idxChordLeft k = idxZero N := by
      apply Fin.ext
      simp only [idxChordLeft, idxZero]
      exact hk0
    let first : Fin N := ⟨0, by omega⟩
    have hright : idxChordRight k = idxInterior first := by
      apply Fin.ext
      simp only [idxChordRight, idxInterior, first]
      omega
    rw [hleft, hright]
    exact candidate_chord_zero hN hq hUpsilon hres
  · by_cases hkN : k.1 = N
    · let lastInterior : Fin N := ⟨N - 1, by omega⟩
      have hleft : idxChordLeft k = idxInterior lastInterior := by
        apply Fin.ext
        simp only [idxChordLeft, idxInterior, lastInterior]
        omega
      have hright : idxChordRight k = idxLast N := by
        apply Fin.ext
        simp only [idxChordRight, idxLast]
        omega
      rw [hleft, hright]
      exact candidate_chord_terminal hN hq hUpsilon
    · let interiorChord : Fin (N - 1) := ⟨k.1 - 1, by omega⟩
      let left : Fin N := ⟨interiorChord.1, by omega⟩
      let right : Fin N := ⟨interiorChord.1 + 1, by omega⟩
      have hleft : idxChordLeft k = idxInterior left := by
        apply Fin.ext
        simp only [idxChordLeft, idxInterior, left, interiorChord]
        omega
      have hright : idxChordRight k = idxInterior right := by
        apply Fin.ext
        simp only [idxChordRight, idxInterior, right, interiorChord]
        omega
      rw [hleft, hright]
      exact candidate_chord_interior hq hUpsilon interiorChord

/-- A zero of the residual produces the complete finite candidate table. -/
theorem candidateData_valid
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hres : shootingResidual N q Upsilon = 0) :
    ValidCoefficients q (candidateData N q Upsilon) where
  upsilon_gt_one := hUpsilon
  a_strict := by
    intro i j hij
    exact candidateA_strict hN hq hUpsilon hres hij
  b_pos := candidateB_pos hN hq hUpsilon hres
  circle := candidate_circle hUpsilon
  chord := candidate_chord hN hq hUpsilon hres
  a_zero := candidateA_zero N q Upsilon
  b_zero := candidateB_zero N q Upsilon
  a_last := candidateA_last N q Upsilon
  b_last := candidateB_last N q Upsilon

end ITEMf
