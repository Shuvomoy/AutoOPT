import ITEMf.Construction.Geometry

/-!
# Necessary direction of the ITEM-f shooting construction

Every valid finite coefficient table determines the prescribed backward
shooting orbit.  In particular, its first angle lies on the target line and
the shooting residual vanishes.
-/

open Set

set_option autoImplicit false

namespace ITEMf

/-- The last interior index, corresponding to manuscript index `N`. -/
def lastInteriorIndex (N : Nat) (hN : 1 ≤ N) : Fin N :=
  ⟨N - 1, by omega⟩

namespace ValidCoefficients

variable {N : Nat} {q : ℝ} {C : CoeffData N}

/-- The final interior ordinate is the positive terminal ordinate prescribed
by the last chord. -/
lemma b_lastInterior
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) :
    C.b (idxInterior (lastInteriorIndex N hN)) =
      Real.sqrt (1 - q) * radius C.Upsilon := by
  let kLast := lastInteriorIndex N hN
  let kChord : Fin (N + 1) := ⟨N, by omega⟩
  have hleft :
      idxChordLeft kChord = idxInterior kLast := by
    apply Fin.ext
    simp [kChord, kLast, lastInteriorIndex, idxChordLeft, idxInterior]
    omega
  have hright :
      idxChordRight kChord = idxLast N := by
    apply Fin.ext
    simp [kChord, idxChordRight, idxLast]
  have hU : 0 < C.Upsilon := zero_lt_one.trans hC.upsilon_gt_one
  have hUne : C.Upsilon ≠ 0 := ne_of_gt hU
  have hR : 0 < radius C.Upsilon := radius_pos hC.upsilon_gt_one
  have hs : 0 < Real.sqrt (1 - q) :=
    Real.sqrt_pos.2 (by linarith [hq.2])
  have hs2 : Real.sqrt (1 - q) ^ 2 = 1 - q :=
    Real.sq_sqrt (by linarith [hq.2])
  have hR2 : radius C.Upsilon ^ 2 = radiusSq C.Upsilon := by
    rw [radius_sq hC.upsilon_gt_one]
  have hchord := hC.chord kChord
  rw [hleft, hright, hC.a_last, hC.b_last] at hchord
  simp [hUne] at hchord
  have hproduct :
      C.b (idxInterior kLast) *
          (Real.sqrt (1 - q) * radius C.Upsilon) =
        (Real.sqrt (1 - q) * radius C.Upsilon) ^ 2 := by
    nlinarith
  have hfactor :
      Real.sqrt (1 - q) * radius C.Upsilon ≠ 0 :=
    ne_of_gt (mul_pos hs hR)
  apply mul_right_cancel₀ hfactor
  simpa [pow_two, kLast] using hproduct

/-- The cosine coordinate of the last interior point is the negative square
root selected by strict ordering. -/
lemma terminal_ratio
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) :
    (C.a (idxInterior (lastInteriorIndex N hN)) - C.Upsilon) /
        radius C.Upsilon =
      -Real.sqrt q := by
  let kLast := lastInteriorIndex N hN
  have hR : 0 < radius C.Upsilon := radius_pos hC.upsilon_gt_one
  have hr : 0 < Real.sqrt q := Real.sqrt_pos.2 hq.1
  have hr2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.1.le
  have hs2 : Real.sqrt (1 - q) ^ 2 = 1 - q :=
    Real.sq_sqrt (by linarith [hq.2])
  have hR2 : radius C.Upsilon ^ 2 = radiusSq C.Upsilon := by
    rw [radius_sq hC.upsilon_gt_one]
  have hcircle := hC.circle kLast
  rw [hC.b_lastInterior hN hq] at hcircle
  have hleft :
      C.a (idxInterior kLast) < C.a (idxLast N) := by
    apply hC.a_strict
    simp [kLast, lastInteriorIndex, idxInterior, idxLast]
    omega
  have hxneg :
      C.a (idxInterior kLast) - C.Upsilon < 0 := by
    rw [hC.a_last] at hleft
    linarith
  have heq :
      C.a (idxInterior kLast) - C.Upsilon =
        -(Real.sqrt q * radius C.Upsilon) := by
    nlinarith [mul_pos hr hR]
  rw [heq]
  field_simp [ne_of_gt hR]

/-- The last interior polar angle is the prescribed terminal angle. -/
lemma coeffAngle_last
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) :
    coeffAngle C (lastInteriorIndex N hN) = terminalAngle q := by
  unfold coeffAngle terminalAngle
  rw [hC.terminal_ratio hN hq]

/-- Consecutive interior polar angles satisfy the exact backward shooting
recurrence. -/
lemma coeffAngle_recurrence
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) (k : Fin (N - 1)) :
    coeffAngle C ⟨k.1, by omega⟩ =
      oneStep q (candidateP q C.Upsilon)
        (coeffAngle C ⟨k.1 + 1, by omega⟩) := by
  let i : Fin N := ⟨k.1, by omega⟩
  let j : Fin N := ⟨k.1 + 1, by omega⟩
  let kChord : Fin (N + 1) := ⟨k.1 + 1, by omega⟩
  let theta := coeffAngle C i
  let phi := coeffAngle C j
  let R := radius C.Upsilon
  have hleft :
      idxChordLeft kChord = idxInterior i := by
    apply Fin.ext
    simp [kChord, i, idxChordLeft, idxInterior]
  have hright :
      idxChordRight kChord = idxInterior j := by
    apply Fin.ext
    simp [kChord, j, idxChordRight, idxInterior]
  have hU : 0 < C.Upsilon := zero_lt_one.trans hC.upsilon_gt_one
  have hUne : C.Upsilon ≠ 0 := ne_of_gt hU
  have hR : 0 < R := by
    dsimp [R]
    exact radius_pos hC.upsilon_gt_one
  have hRne : R ≠ 0 := ne_of_gt hR
  have htheta := hC.coeffAngle_mem_Ioo i
  have hphi := hC.coeffAngle_mem_Ioo j
  have hphitheta : phi < theta := by
    dsimp [theta, phi]
    apply hC.coeffAngle_strictAnti
    simp [i, j]
  have hdiff0 : 0 ≤ theta - phi := by linarith
  have hdiffpi : theta - phi ≤ Real.pi := by
    have hthetaLt : theta < Real.pi := htheta.2
    have hphiPos : 0 < phi := hphi.1
    linarith
  have hchord := hC.chord kChord
  rw [hleft, hright, hC.a_eq_polar i, hC.a_eq_polar j,
    hC.b_eq_polar i, hC.b_eq_polar j] at hchord
  have hR2 : R ^ 2 = radiusSq C.Upsilon := by
    dsimp [R]
    rw [radius_sq hC.upsilon_gt_one]
  rw [← hR2] at hchord
  have hscaled :
      R ^ 2 *
          (Real.cos theta * Real.cos phi +
            Real.sin theta * Real.sin phi) =
        R ^ 2 *
          (1 - q -
            (q * R / C.Upsilon) * Real.cos phi) := by
    dsimp [theta, phi, R] at hchord ⊢
    field_simp [hUne] at hchord ⊢
    ring_nf at hchord ⊢
    nlinarith
  have hdot :
      Real.cos theta * Real.cos phi +
          Real.sin theta * Real.sin phi =
        1 - q - (q * R / C.Upsilon) * Real.cos phi := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 hRne))
    simpa only [mul_assoc] using hscaled
  have hp :
      candidateP q C.Upsilon = q * R / C.Upsilon := by
    dsimp [R]
    exact candidateP_eq_q_mul_radius_div hC.upsilon_gt_one
  have hcos :
      oneStepArg q (candidateP q C.Upsilon) phi =
        Real.cos (theta - phi) := by
    rw [Real.cos_sub, hp]
    unfold oneStepArg
    linarith
  have hacos :
      Real.arccos (oneStepArg q (candidateP q C.Upsilon) phi) =
        theta - phi := by
    rw [hcos, Real.arccos_cos hdiff0 hdiffpi]
  unfold oneStep
  rw [hacos]
  ring

/-- Every interior polar angle of a valid configuration is the corresponding
member of the finite backward shooting orbit. -/
lemma coeffAngle_eq_shootingAngle
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) (k : Fin N) :
    coeffAngle C k = shootingAngle N q C.Upsilon k := by
  rcases N with _ | n
  · omega
  · induction k using Fin.reverseInduction with
    | last =>
        have hterminal :=
          hC.coeffAngle_last (N := n + 1) (by omega) hq
        have hidx :
            lastInteriorIndex (n + 1) (by omega) = Fin.last n := by
          apply Fin.ext
          simp [lastInteriorIndex]
        rw [hidx] at hterminal
        simpa [shootingAngle_eq_iter] using hterminal
    | cast i ih =>
        have hrec :=
          hC.coeffAngle_recurrence (N := n + 1) (by omega) hq i
        have hi :
            (⟨i.1, by omega⟩ : Fin (n + 1)) = i.castSucc := by
          apply Fin.ext
          rfl
        have hj :
            (⟨i.1 + 1, by omega⟩ : Fin (n + 1)) = i.succ := by
          apply Fin.ext
          rfl
        rw [hi, hj] at hrec
        rw [hrec, ih]
        change
          oneStep q (candidateP q C.Upsilon)
              (shootingIter q C.Upsilon (n - (i.1 + 1))) =
            shootingIter q C.Upsilon (n - i.1)
        have hexp :
            n - i.1 = (n - (i.1 + 1)) + 1 := by
          omega
        rw [hexp, shootingIter_succ]

/-- The first coefficient angle is the first shooting-orbit angle. -/
lemma coeffAngle_first_eq_shootingFirst
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) :
    coeffAngle C ⟨0, by omega⟩ =
      shootingFirst N q C.Upsilon := by
  have hfirst :=
    hC.coeffAngle_eq_shootingAngle hN hq (⟨0, by omega⟩ : Fin N)
  simpa [shootingAngle, shootingFirst] using hfirst

/-- The first interior point lies on the target line. -/
lemma coeffAngle_first_line
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) :
    Real.sin (coeffAngle C ⟨0, by omega⟩) =
      Real.sqrt (1 - q) *
        (C.Upsilon +
          radius C.Upsilon *
            Real.cos (coeffAngle C ⟨0, by omega⟩)) := by
  let kFirst : Fin N := ⟨0, by omega⟩
  let kChord : Fin (N + 1) := ⟨0, by omega⟩
  let theta := coeffAngle C kFirst
  let R := radius C.Upsilon
  let s := Real.sqrt (1 - q)
  have hleft :
      idxChordLeft kChord = idxZero N := by
    apply Fin.ext
    simp [kChord, idxChordLeft, idxZero]
  have hright :
      idxChordRight kChord = idxInterior kFirst := by
    apply Fin.ext
    simp [kChord, kFirst, idxChordRight, idxInterior]
  have hU : 0 < C.Upsilon := zero_lt_one.trans hC.upsilon_gt_one
  have hUne : C.Upsilon ≠ 0 := ne_of_gt hU
  have hR : 0 < R := by
    dsimp [R]
    exact radius_pos hC.upsilon_gt_one
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by linarith [hq.2])
  have hs2 : s ^ 2 = 1 - q := by
    dsimp [s]
    exact Real.sq_sqrt (by linarith [hq.2])
  have hR2 : R ^ 2 = C.Upsilon ^ 2 - 1 := by
    dsimp [R]
    exact radius_sq hC.upsilon_gt_one
  have hRspec : radiusSq C.Upsilon = R ^ 2 := by
    unfold radiusSq
    exact hR2.symm
  have hzeroDiff :
      1 / C.Upsilon - C.Upsilon = -(R ^ 2) / C.Upsilon := by
    dsimp [R] at hR2 ⊢
    field_simp [hUne]
    nlinarith
  have hchord := hC.chord kChord
  rw [hleft, hright, hC.a_zero, hC.b_zero,
    hC.a_eq_polar kFirst, hC.b_eq_polar kFirst, hRspec,
    hzeroDiff] at hchord
  have hscaled :
      R ^ 2 *
          (-(R * Real.cos theta) + s * Real.sin theta) =
        R ^ 2 *
          (C.Upsilon -
            (C.Upsilon + R * Real.cos theta) * q) := by
    dsimp [theta, R, s] at hchord ⊢
    field_simp [hUne] at hchord
    ring_nf at hchord ⊢
    exact hchord
  have hbase :
      -(R * Real.cos theta) + s * Real.sin theta =
        C.Upsilon -
          (C.Upsilon + R * Real.cos theta) * q := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hR))
    exact hscaled
  have heq :
      s * Real.sin theta =
        s ^ 2 * (C.Upsilon + R * Real.cos theta) := by
    rw [hs2]
    linarith
  have heq' :
      s * Real.sin theta =
        s * (s * (C.Upsilon + R * Real.cos theta)) := by
    simpa [pow_two, mul_assoc] using heq
  have hline :
      Real.sin theta =
        s * (C.Upsilon + R * Real.cos theta) :=
    mul_left_cancel₀ (ne_of_gt hs) heq'
  exact hline

/-- The first interior angle is the farther target intersection. -/
lemma coeffAngle_first_eq_target
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) :
    coeffAngle C ⟨0, by omega⟩ =
      targetAngleValue q C.Upsilon := by
  let kFirst : Fin N := ⟨0, by omega⟩
  let theta := coeffAngle C kFirst
  let U := C.Upsilon
  let R := radius U
  let r := Real.sqrt q
  let s := Real.sqrt (1 - q)
  let D := q + (1 - q) * U ^ 2
  let a := U + R * Real.cos theta
  have hUgt : 1 < U := by
    dsimp [U]
    exact hC.upsilon_gt_one
  have hU : 0 < U := zero_lt_one.trans hUgt
  have hR : 0 < R := by
    dsimp [R]
    exact radius_pos hUgt
  have hRltU : R < U := by
    dsimp [R]
    exact radius_lt_upsilon hUgt
  have hr : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hq.1
  have hrlt : r < 1 := by
    dsimp [r]
    rw [Real.sqrt_lt' zero_lt_one]
    simpa only [one_pow] using hq.2
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by linarith [hq.2])
  have hD : 0 < D := by
    dsimp [D, U]
    exact targetDenom_pos hq hC.upsilon_gt_one
  have hr2 : r ^ 2 = q := by
    dsimp [r]
    exact Real.sq_sqrt hq.1.le
  have hs2 : s ^ 2 = 1 - q := by
    dsimp [s]
    exact Real.sq_sqrt (by linarith [hq.2])
  have hR2 : R ^ 2 = U ^ 2 - 1 := by
    dsimp [R, U]
    exact radius_sq hC.upsilon_gt_one
  have hline :
      Real.sin theta = s * a := by
    dsimp [theta, s, a, R, U]
    exact hC.coeffAngle_first_line hN hq
  have htrig := Real.sin_sq_add_cos_sq theta
  have hcircle :
      (a - U) ^ 2 + R ^ 2 * (s * a) ^ 2 = R ^ 2 := by
    rw [← hline]
    dsimp [a]
    calc
      (U + R * Real.cos theta - U) ^ 2 +
            R ^ 2 * Real.sin theta ^ 2 =
          R ^ 2 *
            (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by
              ring
      _ = R ^ 2 := by rw [htrig, mul_one]
  have hquad :
      D * a ^ 2 - 2 * U * a + 1 = 0 := by
    ring_nf at hcircle
    rw [hs2, hR2] at hcircle
    dsimp [D]
    ring_nf at hcircle ⊢
    linarith
  have hsquare :
      (D * a - U) ^ 2 = (r * R) ^ 2 := by
    apply sub_eq_zero.mp
    calc
      (D * a - U) ^ 2 - (r * R) ^ 2 =
          D * (D * a ^ 2 - 2 * U * a + 1) := by
            dsimp [D]
            ring_nf
            rw [hr2, hR2]
            ring
      _ = 0 := by rw [hquad, mul_zero]
  have haLower : 1 / U < a := by
    have horder :
        C.a (idxZero N) < C.a (idxInterior kFirst) := by
      apply hC.a_strict
      simp [kFirst, idxZero, idxInterior]
    rw [hC.a_zero, hC.a_eq_polar kFirst] at horder
    exact horder
  have hrRltU : r * R < U :=
    (mul_lt_of_lt_one_left hR hrlt).trans hRltU
  have hnear :
      (U - r * R) / D < 1 / U := by
    rw [div_lt_div_iff₀ hD hU]
    have hprod : 0 < r * R * (U - r * R) :=
      mul_pos (mul_pos hr hR) (sub_pos.mpr hrRltU)
    have hid :
        D - (U - r * R) * U =
          r * R * (U - r * R) := by
      calc
        D - (U - r * R) * U =
            -(q * (U ^ 2 - 1)) + r * R * U := by
              dsimp [D]
              ring
        _ = -(r ^ 2 * R ^ 2) + r * R * U := by
              rw [hr2, hR2]
        _ = r * R * (U - r * R) := by ring
    linarith
  have ha :
      a = (U + r * R) / D := by
    rcases eq_or_eq_neg_of_sq_eq_sq
        (D * a - U) (r * R) hsquare with hplus | hminus
    · apply (eq_div_iff (ne_of_gt hD)).2
      nlinarith
    · have hnearEq : a = (U - r * R) / D := by
        apply (eq_div_iff (ne_of_gt hD)).2
        nlinarith
      exfalso
      rw [hnearEq] at haLower
      exact (not_lt_of_ge hnear.le) haLower
  have hatarget :
      a =
        U + R *
          Real.cos (targetAngleValue q U) := by
    rw [targetAbscissa_eq hq hUgt]
    simpa [r, D] using ha
  have hcos :
      Real.cos theta =
        Real.cos (targetAngleValue q U) := by
    dsimp [a] at hatarget
    have hmul :
        R * Real.cos theta =
          R * Real.cos (targetAngleValue q U) := by
      linarith
    exact mul_left_cancel₀ (ne_of_gt hR) hmul
  have htheta := hC.coeffAngle_mem_Ioo kFirst
  have htarget := targetAngle_range hq hUgt
  apply Real.strictAntiOn_cos.injOn
  · exact ⟨htheta.1.le, htheta.2.le⟩
  · exact ⟨htarget.1.le, htarget.2.le⟩
  · exact hcos

/-- Every valid coefficient table has zero shooting residual. -/
lemma shootingResidual_eq_zero
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) :
    shootingResidual N q C.Upsilon = 0 := by
  have hshoot := hC.coeffAngle_first_eq_shootingFirst hN hq
  have htarget := hC.coeffAngle_first_eq_target hN hq
  unfold shootingResidual
  rw [← hshoot, htarget]
  ring

/-- A valid coefficient table is recovered exactly from the shooting orbit
at its own parameter. -/
lemma eq_candidateData
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) :
    C = candidateData N q C.Upsilon := by
  have ha :
      C.a = candidateA N q C.Upsilon := by
    funext i
    by_cases hi0 : i.1 = 0
    · have hi : i = idxZero N := by
        apply Fin.ext
        simpa [idxZero] using hi0
      rw [hi, hC.a_zero]
      simp
    · by_cases hiLast : i.1 = N + 1
      · have hi : i = idxLast N := by
          apply Fin.ext
          simpa [idxLast] using hiLast
        rw [hi, hC.a_last]
        simp
      · let k : Fin N := ⟨i.1 - 1, by omega⟩
        have hi : i = idxInterior k := by
          apply Fin.ext
          simp [k, idxInterior]
          omega
        rw [hi]
        change
          C.a (idxInterior k) =
            candidateA N q C.Upsilon (idxInterior k)
        rw [hC.a_eq_polar k, candidateA_interior,
          hC.coeffAngle_eq_shootingAngle hN hq k]
  have hb :
      C.b = candidateB N q C.Upsilon := by
    funext i
    by_cases hi0 : i.1 = 0
    · have hi : i = idxZero N := by
        apply Fin.ext
        simpa [idxZero] using hi0
      rw [hi, hC.b_zero]
      simp
    · by_cases hiLast : i.1 = N + 1
      · have hi : i = idxLast N := by
          apply Fin.ext
          simpa [idxLast] using hiLast
        rw [hi, hC.b_last]
        simp
      · let k : Fin N := ⟨i.1 - 1, by omega⟩
        have hi : i = idxInterior k := by
          apply Fin.ext
          simp [k, idxInterior]
          omega
        rw [hi]
        change
          C.b (idxInterior k) =
            candidateB N q C.Upsilon (idxInterior k)
        rw [hC.b_eq_polar k, candidateB_interior,
          hC.coeffAngle_eq_shootingAngle hN hq k]
  cases C with
  | mk U a b =>
      change
        ({ Upsilon := U, a := a, b := b } : CoeffData N) =
          { Upsilon := U,
            a := candidateA N q U,
            b := candidateB N q U }
      rw [CoeffData.mk.injEq]
      exact ⟨rfl, ha, hb⟩

/-- Two valid tables with the same shooting parameter coincide. -/
lemma eq_of_upsilon_eq
    (hN : 1 ≤ N) (hq : UnitRatio q)
    {C' : CoeffData N}
    (hC : ValidCoefficients q C)
    (hC' : ValidCoefficients q C')
    (hUpsilon : C.Upsilon = C'.Upsilon) :
    C = C' := by
  rw [hC.eq_candidateData hN hq, hC'.eq_candidateData hN hq,
    hUpsilon]

end ValidCoefficients

namespace Internal

/-- Necessary direction of the fixed-parameter shooting equivalence. -/
theorem validCoefficients_shootingResidual
    (N : Nat) (q : ℝ) (hN : 1 ≤ N) (hq : UnitRatio q)
    (C : CoeffData N) (hC : ValidCoefficients q C) :
    shootingResidual N q C.Upsilon = 0 :=
  hC.shootingResidual_eq_zero hN hq

end Internal

end ITEMf
