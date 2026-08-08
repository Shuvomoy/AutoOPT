import ITEMf.Construction.Shooting

/-!
# Reversal symmetry of the ITEM-f construction

The inversion `T (a,b) = (1/a,b/a)` preserves the construction circle and
turns every chord into the corresponding reversed chord.  Applying fixed
shooting-parameter uniqueness to the reversed table proves the two coordinate
identities used by the algorithmic and Lyapunov developments.
-/

set_option autoImplicit false

namespace ITEMf

/-- Reverse a coefficient table and apply the manuscript's circle inversion. -/
noncomputable def reversedTable {N : Nat} (C : CoeffData N) : CoeffData N where
  Upsilon := C.Upsilon
  a k := 1 / C.a (reverseIndex k)
  b k := C.b (reverseIndex k) / C.a (reverseIndex k)

@[simp] lemma reversedTable_upsilon
    {N : Nat} (C : CoeffData N) :
    (reversedTable C).Upsilon = C.Upsilon := rfl

lemma reverseIndex_idxZero (N : Nat) :
    reverseIndex (idxZero N) = idxLast N := by
  apply Fin.ext
  simp [reverseIndex, idxZero, idxLast, Fin.rev]

lemma reverseIndex_idxLast (N : Nat) :
    reverseIndex (idxLast N) = idxZero N := by
  apply Fin.ext
  simp [reverseIndex, idxZero, idxLast, Fin.rev]

lemma reverseIndex_idxInterior
    {N : Nat} (k : Fin N) :
    reverseIndex (idxInterior k) = idxInterior (Fin.rev k) := by
  apply Fin.ext
  simp [reverseIndex, idxInterior, Fin.rev]
  omega

lemma reverseIndex_idxChordLeft
    {N : Nat} (k : Fin (N + 1)) :
    reverseIndex (idxChordLeft k) =
      idxChordRight (Fin.rev k) := by
  apply Fin.ext
  simp [reverseIndex, idxChordLeft, idxChordRight, Fin.rev]
  omega

lemma reverseIndex_idxChordRight
    {N : Nat} (k : Fin (N + 1)) :
    reverseIndex (idxChordRight k) =
      idxChordLeft (Fin.rev k) := by
  apply Fin.ext
  simp [reverseIndex, idxChordLeft, idxChordRight, Fin.rev]

namespace ValidCoefficients

variable {N : Nat} {q : ℝ} {C : CoeffData N}

/-- Every first coordinate in a valid table is positive. -/
lemma a_pos (hC : ValidCoefficients q C) (i : Fin (N + 2)) :
    0 < C.a i := by
  have hU : 0 < C.Upsilon := zero_lt_one.trans hC.upsilon_gt_one
  have hzero : 0 < C.a (idxZero N) := by
    rw [hC.a_zero]
    exact one_div_pos.mpr hU
  by_cases hi : i.1 = 0
  · have hieq : i = idxZero N := by
      apply Fin.ext
      simpa [idxZero] using hi
    simpa [hieq] using hzero
  · have hidx : (idxZero N).1 < i.1 := by
      change 0 < i.1
      omega
    exact hzero.trans (hC.a_strict hidx)

/-- Circle inversion preserves the circle equation at every interior point. -/
lemma reversedTable_circle
    (hC : ValidCoefficients q C) (k : Fin N) :
    ((reversedTable C).a (idxInterior k) -
          (reversedTable C).Upsilon) ^ 2 +
        (reversedTable C).b (idxInterior k) ^ 2 =
      radiusSq (reversedTable C).Upsilon := by
  let j : Fin N := Fin.rev k
  have hrev :
      reverseIndex (idxInterior k) = idxInterior j := by
    simpa [j] using reverseIndex_idxInterior k
  have ha : 0 < C.a (idxInterior j) := hC.a_pos _
  have hcircle := hC.circle j
  change
    (1 / C.a (reverseIndex (idxInterior k)) - C.Upsilon) ^ 2 +
        (C.b (reverseIndex (idxInterior k)) /
          C.a (reverseIndex (idxInterior k))) ^ 2 =
      radiusSq C.Upsilon
  rw [hrev]
  unfold radiusSq at hcircle ⊢
  field_simp [ne_of_gt ha]
  nlinarith

/-- Circle inversion sends an original chord to the reversed chord. -/
lemma reversedTable_chord
    (hC : ValidCoefficients q C) (k : Fin (N + 1)) :
    ((reversedTable C).a (idxChordLeft k) -
          (reversedTable C).Upsilon) *
          ((reversedTable C).a (idxChordRight k) -
            (reversedTable C).Upsilon) +
        (reversedTable C).b (idxChordLeft k) *
          (reversedTable C).b (idxChordRight k) =
      radiusSq (reversedTable C).Upsilon *
        (1 - q * (reversedTable C).a (idxChordRight k) /
          (reversedTable C).Upsilon) := by
  let j : Fin (N + 1) := Fin.rev k
  have hrevLeft :
      reverseIndex (idxChordLeft k) = idxChordRight j := by
    simpa [j] using reverseIndex_idxChordLeft k
  have hrevRight :
      reverseIndex (idxChordRight k) = idxChordLeft j := by
    simpa [j] using reverseIndex_idxChordRight k
  have ha : 0 < C.a (idxChordLeft j) := hC.a_pos _
  have ha' : 0 < C.a (idxChordRight j) := hC.a_pos _
  have hU : 0 < C.Upsilon :=
    zero_lt_one.trans hC.upsilon_gt_one
  have hchord := hC.chord j
  change
    (1 / C.a (reverseIndex (idxChordLeft k)) - C.Upsilon) *
          (1 / C.a (reverseIndex (idxChordRight k)) - C.Upsilon) +
        (C.b (reverseIndex (idxChordLeft k)) /
            C.a (reverseIndex (idxChordLeft k))) *
          (C.b (reverseIndex (idxChordRight k)) /
            C.a (reverseIndex (idxChordRight k))) =
      radiusSq C.Upsilon *
        (1 - q * (1 / C.a (reverseIndex (idxChordRight k))) /
          C.Upsilon)
  rw [hrevLeft, hrevRight]
  unfold radiusSq at hchord ⊢
  field_simp [ne_of_gt ha, ne_of_gt ha', ne_of_gt hU] at hchord ⊢
  ring_nf at hchord ⊢
  nlinarith

/-- The reversed and inverted table satisfies the full construction. -/
lemma reversedTable_valid
    (hC : ValidCoefficients q C) :
    ValidCoefficients q (reversedTable C) := by
  have hU : 0 < C.Upsilon :=
    zero_lt_one.trans hC.upsilon_gt_one
  refine
    { upsilon_gt_one := hC.upsilon_gt_one
      a_strict := ?_
      b_pos := ?_
      circle := hC.reversedTable_circle
      chord := hC.reversedTable_chord
      a_zero := ?_
      b_zero := ?_
      a_last := ?_
      b_last := ?_ }
  · intro i j hij
    have hrev :
        (reverseIndex j).1 < (reverseIndex i).1 := by
      simp [reverseIndex, Fin.rev]
      omega
    have horder :
        C.a (reverseIndex j) < C.a (reverseIndex i) :=
      hC.a_strict hrev
    have hai : 0 < C.a (reverseIndex i) := hC.a_pos _
    have haj : 0 < C.a (reverseIndex j) := hC.a_pos _
    change 1 / C.a (reverseIndex i) < 1 / C.a (reverseIndex j)
    exact one_div_lt_one_div_of_lt haj horder
  · intro i
    exact div_pos (hC.b_pos _) (hC.a_pos _)
  · change 1 / C.a (reverseIndex (idxZero N)) = 1 / C.Upsilon
    rw [reverseIndex_idxZero, hC.a_last]
  · change
      C.b (reverseIndex (idxZero N)) /
          C.a (reverseIndex (idxZero N)) =
        Real.sqrt (1 - q) * radius C.Upsilon / C.Upsilon
    rw [reverseIndex_idxZero, hC.a_last, hC.b_last]
  · change 1 / C.a (reverseIndex (idxLast N)) = C.Upsilon
    rw [reverseIndex_idxLast, hC.a_zero]
    field_simp [ne_of_gt hU]
  · change
      C.b (reverseIndex (idxLast N)) /
          C.a (reverseIndex (idxLast N)) =
        Real.sqrt (1 - q) * radius C.Upsilon
    rw [reverseIndex_idxLast, hC.a_zero, hC.b_zero]
    field_simp [ne_of_gt hU]

end ValidCoefficients

namespace Internal

/-- Reversal and inversion of the unique construction table give the two
manuscript coordinate identities. -/
theorem involutionSymmetry
    {N : Nat} {q : ℝ} (hN : 1 ≤ N) (hq : UnitRatio q)
    (C : CoeffData N) (hC : ValidCoefficients q C) :
    InvolutionSymmetryResult C := by
  have hrevValid :
      ValidCoefficients q (reversedTable C) :=
    hC.reversedTable_valid
  have heq :
      C = reversedTable C :=
    hC.eq_of_upsilon_eq hN hq hrevValid rfl
  intro k
  have ha :
      C.a k = 1 / C.a (reverseIndex k) := by
    exact congrFun (congrArg CoeffData.a heq) k
  have hb :
      C.b k =
        C.b (reverseIndex k) / C.a (reverseIndex k) := by
    exact congrFun (congrArg CoeffData.b heq) k
  have harev : C.a (reverseIndex k) ≠ 0 :=
    ne_of_gt (hC.a_pos _)
  constructor
  · rw [ha]
    field_simp
  · rw [ha, hb]
    field_simp

end Internal
end ITEMf
