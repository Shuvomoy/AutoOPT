import ITEMf.Algorithm.CoefficientLemmas
import ITEMf.Construction.Symmetry

/-!
# ITEM-f coordinate relations

The main construction-to-coordinate theorem is completed after the geometric
shooting modules.  This file also records the exact interior denominator
facts consumed by the Lyapunov algebra.
-/

set_option autoImplicit false

namespace ITEMf

variable {N : Nat}

private theorem reverse_lyapNext_eq_phiLeft
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    reverseIndex (lyapNextCoeffIndex j) =
      idxChordLeft (lyapPhiIndex j) := by
  dsimp only
  apply Fin.ext
  simp [reverseIndex, lyapNextCoeffIndex, lyapPhiIndex,
    interiorLyapIndex, idxChordLeft, Fin.rev]
  omega

private theorem interior_phi_sq_of_symmetry
    {q : ℝ} (hq : UnitRatio q) {C : CoeffData N}
    (hC : ValidCoefficients q C)
    (hsym : InvolutionSymmetryResult C)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    phi q C (lyapPhiIndex j) ^ 2 =
      2 * C.Upsilon *
          C.a (reverseIndex (lyapNextCoeffIndex j)) - q := by
  dsimp only
  let j := interiorLyapIndex i
  let Aidx := lyapNextCoeffIndex j
  let ridx := reverseIndex Aidx
  let pidx := lyapPhiIndex j
  have hrev : ridx = idxChordLeft pidx := by
    dsimp [ridx, Aidx, pidx, j]
    exact reverse_lyapNext_eq_phiLeft i
  have hp0 : pidx.1 ≠ 0 := by
    dsimp [pidx, j, lyapPhiIndex, interiorLyapIndex]
    omega
  have hpN : pidx.1 ≠ N := by
    dsimp [pidx, j, lyapPhiIndex, interiorLyapIndex]
    omega
  have hp0' :
      (lyapPhiIndex (interiorLyapIndex i)).1 ≠ 0 := by
    simpa [pidx, j] using hp0
  have hpN' :
      (lyapPhiIndex (interiorLyapIndex i)).1 ≠ N := by
    simpa [pidx, j] using hpN
  have hA : 0 < C.a Aidx := hC.a_pos _
  have hU : 0 < C.Upsilon := hC.upsilon_pos
  have hAlast :
      Aidx.1 < (idxLast N).1 := by
    dsimp [Aidx, j, lyapNextCoeffIndex, interiorLyapIndex, idxLast]
    omega
  have hAU : C.a Aidx < C.Upsilon := by
    have h := hC.a_strict hAlast
    simpa [hC.a_last] using h
  have hrpos : 0 < C.a ridx := hC.a_pos _
  have hprod : C.a Aidx * C.a ridx = 1 :=
    (hsym Aidx).1
  have hr :
      C.a ridx = 1 / C.a Aidx := by
    field_simp [ne_of_gt hA]
    nlinarith [hprod]
  have hrad :
      0 < 2 * C.Upsilon * C.a ridx - q := by
    rw [hr]
    have hratio : 1 < C.Upsilon / C.a Aidx :=
      (one_lt_div (hA)).2 hAU
    have htwo : 2 < 2 * (C.Upsilon / C.a Aidx) := by
      linarith
    field_simp [ne_of_gt hA] at htwo ⊢
    nlinarith [hq.2]
  unfold phi
  simp only [hp0', hpN', if_false]
  rw [← hrev]
  exact Real.sq_sqrt hrad.le

private theorem interior_s_pos_of_symmetry
    {q : ℝ} (hq : UnitRatio q) {C : CoeffData N}
    (hC : ValidCoefficients q C)
    (hsym : InvolutionSymmetryResult C)
    (i : Fin (N - 1)) :
    0 < sCoeff q C (interiorLyapIndex i) := by
  let j := interiorLyapIndex i
  have hphiSq :=
    interior_phi_sq_of_symmetry hq hC hsym i
  dsimp only at hphiSq
  have hrpos :
      0 < C.a (reverseIndex (lyapNextCoeffIndex j)) :=
    hC.a_pos _
  have hA : 0 < C.a (lyapNextCoeffIndex j) := hC.a_pos _
  have hU : 0 < C.Upsilon := hC.upsilon_pos
  have hprod :
      C.a (lyapNextCoeffIndex j) *
          C.a (reverseIndex (lyapNextCoeffIndex j)) = 1 :=
    (hsym (lyapNextCoeffIndex j)).1
  have hAU : C.a (lyapNextCoeffIndex j) < C.Upsilon := by
    have hindex :
        (lyapNextCoeffIndex j).1 < (idxLast N).1 := by
      simp [j, interiorLyapIndex, lyapNextCoeffIndex, idxLast]
      omega
    have h := hC.a_strict hindex
    simpa [hC.a_last] using h
  have hrad :
      0 < 2 * C.Upsilon *
          C.a (reverseIndex (lyapNextCoeffIndex j)) - q := by
    have hratio :
        1 < C.Upsilon /
          C.a (lyapNextCoeffIndex j) :=
      (one_lt_div hA).2 hAU
    have hr :
        C.a (reverseIndex (lyapNextCoeffIndex j)) =
          1 / C.a (lyapNextCoeffIndex j) := by
      field_simp [ne_of_gt hA]
      nlinarith [hprod]
    rw [hr]
    have : 2 < 2 * (C.Upsilon /
        C.a (lyapNextCoeffIndex j)) := by linarith
    field_simp [ne_of_gt hA] at this ⊢
    nlinarith [hq.2]
  have hphi :
      0 < phi q C (lyapPhiIndex j) := by
    have hnonneg : 0 ≤ phi q C (lyapPhiIndex j) := by
      let pidx := lyapPhiIndex j
      have hp0 : pidx.1 ≠ 0 := by
        dsimp [pidx, j, lyapPhiIndex, interiorLyapIndex]
        omega
      have hpN : pidx.1 ≠ N := by
        dsimp [pidx, j, lyapPhiIndex, interiorLyapIndex]
        omega
      change (lyapPhiIndex j).1 ≠ 0 at hp0
      change (lyapPhiIndex j).1 ≠ N at hpN
      unfold phi
      simp only [hp0, hpN, if_false]
      exact Real.sqrt_nonneg _
    nlinarith [hphiSq]
  unfold sCoeff
  exact div_pos
    (mul_pos
      (mul_pos (Real.sqrt_pos.2 hq.1) hA)
      hphi)
    hU

private theorem interior_unit_of_symmetry
    {q : ℝ} (hq : UnitRatio q) {C : CoeffData N}
    (hC : ValidCoefficients q C)
    (hsym : InvolutionSymmetryResult C)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    sCoeff q C j ^ 2 + cCoeff q C j ^ 2 = 1 := by
  dsimp only
  let j := interiorLyapIndex i
  let A := C.a (lyapNextCoeffIndex j)
  let Ar := C.a (reverseIndex (lyapNextCoeffIndex j))
  have hphiSq :=
    interior_phi_sq_of_symmetry hq hC hsym i
  dsimp only at hphiSq
  change
    phi q C (lyapPhiIndex j) ^ 2 =
      2 * C.Upsilon * Ar - q at hphiSq
  have hA : A ≠ 0 := by
    dsimp [A]
    exact hC.a_ne_zero _
  have hU : C.Upsilon ≠ 0 := hC.upsilon_ne_zero
  have hsqrt :
      Real.sqrt q ^ 2 = q :=
    Real.sq_sqrt hq.1.le
  have hprod : A * Ar = 1 := by
    simpa [A, Ar] using
      (hsym (lyapNextCoeffIndex j)).1
  have hAr : Ar = 1 / A := by
    field_simp [hA]
    nlinarith [hprod]
  unfold sCoeff cCoeff
  change
    (Real.sqrt q * A *
        phi q C (lyapPhiIndex j) / C.Upsilon) ^ 2 +
      (1 - q * A / C.Upsilon) ^ 2 = 1
  simp only [mul_pow, div_pow]
  rw [hphiSq, hsqrt, hAr]
  field_simp [hA, hU]
  ring

private theorem interior_rotation_x_relations
    {q : ℝ} (hq : UnitRatio q) {C : CoeffData N}
    (hN : 1 ≤ N) (hC : ValidCoefficients q C)
    (hsym : InvolutionSymmetryResult C)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    let n := nextInteriorLyapIndex i
    cCoeff q C j *
          (C.a (lyapCoeffIndex j) - C.Upsilon) +
        sCoeff q C j * C.b (lyapCoeffIndex j) =
      C.a (lyapNextCoeffIndex j) - C.Upsilon ∧
    C.a (lyapCoeffIndex j) - C.Upsilon =
      cCoeff q C j *
          (C.a (lyapNextCoeffIndex j) - C.Upsilon) -
        sCoeff q C j * C.b (lyapNextCoeffIndex j) := by
  dsimp only
  let j := interiorLyapIndex i
  let n := nextInteriorLyapIndex i
  let theta := coeffAngle C j
  let psi := coeffAngle C n
  let delta := theta - psi
  let c := cCoeff q C j
  let s := sCoeff q C j
  have hleft :
      lyapCoeffIndex j = idxInterior j := by
    apply Fin.ext
    rfl
  have hright :
      lyapNextCoeffIndex j = idxInterior n := by
    apply Fin.ext
    rfl
  have htheta :
      theta ∈ Set.Ioo (0 : ℝ) Real.pi := by
    dsimp [theta]
    exact hC.coeffAngle_mem_Ioo j
  have hpsi :
      psi ∈ Set.Ioo (0 : ℝ) Real.pi := by
    dsimp [psi]
    exact hC.coeffAngle_mem_Ioo n
  have hpsitheta : psi < theta := by
    dsimp [psi, theta]
    apply hC.coeffAngle_strictAnti
    simp [j, n, interiorLyapIndex, nextInteriorLyapIndex]
  have hdelta0 : 0 < delta := by
    dsimp [delta]
    linarith
  have hdeltapi : delta < Real.pi := by
    dsimp [delta]
    linarith [htheta.2, hpsi.1]
  have hrec := hC.coeffAngle_recurrence hN hq i
  have hrec' :
      theta =
        oneStep q (candidateP q C.Upsilon) psi := by
    have hi :
        (⟨i.1, by omega⟩ : Fin N) = j := by
      apply Fin.ext
      rfl
    have hin :
        (⟨i.1 + 1, by omega⟩ : Fin N) = n := by
      apply Fin.ext
      rfl
    rw [hi, hin] at hrec
    exact hrec
  have hp0 := candidateP_pos hq hC.upsilon_gt_one
  have hpq := candidateP_lt_q hq hC.upsilon_gt_one
  have harg :=
    oneStepArg_mem_Ioo hq hp0 hpq psi
  have hdelta :
      delta =
        Real.arccos
          (oneStepArg q (candidateP q C.Upsilon) psi) := by
    dsimp [delta]
    rw [hrec']
    unfold oneStep
    ring
  have hcos :
      Real.cos delta = c := by
    rw [hdelta, Real.cos_arccos harg.1.le harg.2.le]
    unfold oneStepArg
    rw [candidateP_eq_q_mul_radius_div hC.upsilon_gt_one]
    have hpolar := hC.a_eq_polar n
    rw [← hright] at hpolar
    dsimp [psi, c, cCoeff]
    rw [hpolar]
    field_simp [hC.upsilon_ne_zero]
    ring
  have hunit :
      s ^ 2 + c ^ 2 = 1 := by
    simpa [s, c, j] using
      interior_unit_of_symmetry hq hC hsym i
  have hspos : 0 < s := by
    simpa [s, j] using
      interior_s_pos_of_symmetry hq hC hsym i
  have hsindelta : 0 < Real.sin delta :=
    Real.sin_pos_of_pos_of_lt_pi hdelta0 hdeltapi
  have htrig := Real.sin_sq_add_cos_sq delta
  have hsin : Real.sin delta = s := by
    rw [hcos] at htrig
    nlinarith
  have hak := hC.a_eq_polar j
  have hbk := hC.b_eq_polar j
  have hak1 := hC.a_eq_polar n
  have hbk1 := hC.b_eq_polar n
  rw [← hleft] at hak hbk
  rw [← hright] at hak1 hbk1
  constructor
  · rw [hak, hbk, hak1]
    change
      c * (C.Upsilon + radius C.Upsilon * Real.cos theta -
          C.Upsilon) +
        s * (radius C.Upsilon * Real.sin theta) =
      C.Upsilon + radius C.Upsilon * Real.cos psi -
        C.Upsilon
    rw [← hcos, ← hsin]
    have hangle : theta - delta = psi := by
      dsimp [delta]
      ring
    have hcosSub :
        Real.cos (theta - delta) =
          Real.cos theta * Real.cos delta +
            Real.sin theta * Real.sin delta :=
      Real.cos_sub theta delta
    calc
      Real.cos delta *
            (C.Upsilon + radius C.Upsilon * Real.cos theta -
              C.Upsilon) +
          Real.sin delta *
            (radius C.Upsilon * Real.sin theta) =
          radius C.Upsilon * Real.cos (theta - delta) := by
            rw [hcosSub]
            ring
      _ = radius C.Upsilon * Real.cos psi := by rw [hangle]
      _ = C.Upsilon + radius C.Upsilon * Real.cos psi -
          C.Upsilon := by ring
  · rw [hak, hak1, hbk1]
    change
      C.Upsilon + radius C.Upsilon * Real.cos theta -
          C.Upsilon =
        c * (C.Upsilon + radius C.Upsilon * Real.cos psi -
            C.Upsilon) -
          s * (radius C.Upsilon * Real.sin psi)
    rw [← hcos, ← hsin]
    have hangle : psi + delta = theta := by
      dsimp [delta]
      ring
    have hcosAdd :
        Real.cos (psi + delta) =
          Real.cos psi * Real.cos delta -
            Real.sin psi * Real.sin delta :=
      Real.cos_add psi delta
    calc
      C.Upsilon + radius C.Upsilon * Real.cos theta -
          C.Upsilon =
          radius C.Upsilon * Real.cos (psi + delta) := by
            rw [hangle]
            ring
      _ =
          Real.cos delta *
              (C.Upsilon + radius C.Upsilon * Real.cos psi -
                C.Upsilon) -
            Real.sin delta *
              (radius C.Upsilon * Real.sin psi) := by
            rw [hcosAdd]
            ring

private theorem interior_forward_of_symmetry
    {q : ℝ} (hq : UnitRatio q) {C : CoeffData N}
    (hN : 1 ≤ N) (hC : ValidCoefficients q C)
    (hsym : InvolutionSymmetryResult C)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    cCoeff q C j * C.a (lyapCoeffIndex j) +
        sCoeff q C j * C.b (lyapCoeffIndex j) =
      (1 - q) * C.a (lyapNextCoeffIndex j) := by
  dsimp only
  let j := interiorLyapIndex i
  have hrotation :=
    (interior_rotation_x_relations hq hN hC hsym i).1
  have hc :
      (1 - cCoeff q C j) * C.Upsilon =
        q * C.a (lyapNextCoeffIndex j) := by
    unfold cCoeff
    field_simp [hC.upsilon_ne_zero]
    ring
  nlinarith

private theorem interior_inverse_of_symmetry
    {q : ℝ} (hq : UnitRatio q) {C : CoeffData N}
    (hN : 1 ≤ N) (hC : ValidCoefficients q C)
    (hsym : InvolutionSymmetryResult C)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    C.a (lyapCoeffIndex j) =
      (cCoeff q C j + q) * C.a (lyapNextCoeffIndex j) -
        sCoeff q C j * C.b (lyapNextCoeffIndex j) := by
  dsimp only
  let j := interiorLyapIndex i
  have hrotation :=
    (interior_rotation_x_relations hq hN hC hsym i).2
  have hc :
      (1 - cCoeff q C j) * C.Upsilon =
        q * C.a (lyapNextCoeffIndex j) := by
    unfold cCoeff
    field_simp [hC.upsilon_ne_zero]
    ring
  nlinarith

namespace Internal

/-- Scalar rotation, reversal, and endpoint relations for the ITEM-f
construction. -/
theorem coordinateRelations
    (N : Nat) (q : ℝ) (hN : 1 ≤ N) (hq : UnitRatio q)
    (C : CoeffData N) (hC : ValidCoefficients q C) :
    CoordinateRelationsResult q C hN := by
  have hsym :=
    ITEMf.Internal.involutionSymmetry hN hq C hC
  let t := terminalLyapIndex hN
  have htCoeff :
      lyapCoeffIndex t = idxN N :=
    lyapCoeffIndex_terminal hN
  have htNext :
      lyapNextCoeffIndex t = idxLast N :=
    lyapNextCoeffIndex_terminal hN
  have htPhi :
      lyapPhiIndex t =
        (⟨0, by omega⟩ : Fin (N + 1)) :=
    lyapPhiIndex_terminal hN
  have hterminalC :
      cCoeff q C t = 1 - q := by
    unfold cCoeff
    rw [htNext, hC.a_last]
    field_simp [hC.upsilon_ne_zero]
  have hterminalS :
      sCoeff q C t =
        Real.sqrt q * Real.sqrt (1 - q) := by
    unfold sCoeff
    rw [htNext, htPhi, hC.a_last, phi_zero]
    field_simp [hC.upsilon_ne_zero]
  have hlastIndex :
      idxInterior (lastInteriorIndex N hN) = idxN N := by
    apply Fin.ext
    simp [lastInteriorIndex, idxInterior, idxN]
    omega
  have hbN :
      C.b (idxN N) =
        radius C.Upsilon * Real.sqrt (1 - q) := by
    have hb := hC.b_lastInterior hN hq
    rw [hlastIndex] at hb
    nlinarith
  have haN :
      C.a (idxN N) =
        C.Upsilon - radius C.Upsilon * Real.sqrt q := by
    have ha := hC.terminal_ratio hN hq
    rw [hlastIndex] at ha
    have hR :
        radius C.Upsilon ≠ 0 :=
      ne_of_gt (radius_pos hC.upsilon_gt_one)
    field_simp [hR] at ha
    nlinarith
  have hterminalForward :
      cCoeff q C t * C.a (lyapCoeffIndex t) +
          sCoeff q C t * C.b (lyapCoeffIndex t) =
        (1 - q) * C.a (lyapNextCoeffIndex t) := by
    rw [htCoeff, htNext, hterminalC, hterminalS,
      haN, hbN, hC.a_last]
    have hsquare :
        Real.sqrt (1 - q) ^ 2 = 1 - q :=
      Real.sq_sqrt (sub_nonneg.mpr hq.2.le)
    calc
      (1 - q) *
            (C.Upsilon - radius C.Upsilon * Real.sqrt q) +
          Real.sqrt q * Real.sqrt (1 - q) *
            (radius C.Upsilon * Real.sqrt (1 - q)) =
          (1 - q) *
              (C.Upsilon - radius C.Upsilon * Real.sqrt q) +
            Real.sqrt q * radius C.Upsilon *
              Real.sqrt (1 - q) ^ 2 := by ring
      _ = (1 - q) * C.Upsilon := by rw [hsquare]; ring
  have hfirstReverse :
      reverseIndex
          (lyapCoeffIndex (firstLyapIndex hN)) =
        idxN N := by
    apply Fin.ext
    simp [reverseIndex, lyapCoeffIndex, firstLyapIndex,
      idxN, Fin.rev]
  refine
    {
      forward := ?_
      inverse := interior_inverse_of_symmetry hq hN hC hsym
      interior_unit := interior_unit_of_symmetry hq hC hsym
      mirror_next := ?_
      first_last := ?_
      first_b := ?_
      terminal_c := hterminalC
      terminal_s := hterminalS
    }
  · intro k
    by_cases hk : k.1 = N - 1
    · have hkt : k = t := by
        apply Fin.ext
        simpa [t, terminalLyapIndex] using hk
      simpa [hkt] using hterminalForward
    · have hki : k.1 < N - 1 := by omega
      let i : Fin (N - 1) := ⟨k.1, hki⟩
      have hik : interiorLyapIndex i = k := by
        apply Fin.ext
        rfl
      simpa [hik] using
        interior_forward_of_symmetry hq hN hC hsym i
  · intro i
    exact (hsym (lyapNextCoeffIndex (interiorLyapIndex i))).1
  · have h :=
      (hsym (lyapCoeffIndex (firstLyapIndex hN))).1
    rw [hfirstReverse] at h
    exact h
  · have h :=
      (hsym (lyapCoeffIndex (firstLyapIndex hN))).2
    rw [hfirstReverse] at h
    exact h

end Internal

theorem interior_c_pos
    {q : ℝ} (hq : UnitRatio q) {C : CoeffData N}
    (hC : ValidCoefficients q C) (i : Fin (N - 1)) :
    0 < cCoeff q C (interiorLyapIndex i) := by
  let j := interiorLyapIndex i
  let A := C.a (lyapNextCoeffIndex j)
  have hU : 0 < C.Upsilon := hC.upsilon_pos
  have hA : 0 < A := hC.a_pos _
  have hindex :
      (lyapNextCoeffIndex j).1 < (idxLast N).1 := by
    simp [j, interiorLyapIndex, lyapNextCoeffIndex, idxLast]
    omega
  have hAU : A < C.Upsilon := by
    have := hC.a_strict hindex
    simpa [A, hC.a_last] using this
  have hratio : 0 < q * A / C.Upsilon :=
    div_pos (mul_pos hq.1 hA) hU
  have hqA_lt : q * A / C.Upsilon < 1 := by
    have hAdiv : A / C.Upsilon < 1 :=
      (div_lt_one hU).2 hAU
    have hAdiv_pos : 0 < A / C.Upsilon := div_pos hA hU
    calc
      q * A / C.Upsilon = q * (A / C.Upsilon) := by ring
      _ < 1 * (A / C.Upsilon) :=
        mul_lt_mul_of_pos_right hq.2 hAdiv_pos
      _ < 1 := by simpa using hAdiv
  unfold cCoeff
  linarith

theorem interior_c_lt_one
    {q : ℝ} (hq : UnitRatio q) {C : CoeffData N}
    (hC : ValidCoefficients q C) (i : Fin (N - 1)) :
    cCoeff q C (interiorLyapIndex i) < 1 := by
  have hU : 0 < C.Upsilon := hC.upsilon_pos
  have hA : 0 < C.a (lyapNextCoeffIndex (interiorLyapIndex i)) :=
    hC.a_pos _
  unfold cCoeff
  have : 0 < q * C.a (lyapNextCoeffIndex (interiorLyapIndex i)) /
      C.Upsilon :=
    div_pos (mul_pos hq.1 hA) hU
  linarith

theorem interior_s_ne_zero_of_relations
    {q : ℝ} (hq : UnitRatio q) {C : CoeffData N}
    (hC : ValidCoefficients q C) (hN : 1 ≤ N)
    (hcoord : CoordinateRelationsResult q C hN)
    (i : Fin (N - 1)) :
    sCoeff q C (interiorLyapIndex i) ≠ 0 := by
  let j := interiorLyapIndex i
  have hc0 : 0 < cCoeff q C j := interior_c_pos hq hC i
  have hc1 : cCoeff q C j < 1 := interior_c_lt_one hq hC i
  have hunit := hcoord.interior_unit i
  dsimp [j] at hunit
  intro hs
  rw [hs] at hunit
  norm_num at hunit
  rcases hunit with hunit | hunit
  · linarith
  · linarith

theorem s_ne_zero_of_relations
    {q : ℝ} (hq : UnitRatio q) {C : CoeffData N}
    (hC : ValidCoefficients q C) (hN : 1 ≤ N)
    (hcoord : CoordinateRelationsResult q C hN)
    (i : Fin N) :
    sCoeff q C i ≠ 0 := by
  by_cases hi : i.1 = N - 1
  · have hit : i = terminalLyapIndex hN := by
      apply Fin.ext
      simpa [terminalLyapIndex] using hi
    rw [hit, hcoord.terminal_s]
    exact mul_ne_zero
      (ne_of_gt (Real.sqrt_pos.2 hq.1))
      (ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr hq.2)))
  · have hirange : i.1 < N - 1 := by omega
    let k : Fin (N - 1) := ⟨i.1, hirange⟩
    have hik : interiorLyapIndex k = i := by
      apply Fin.ext
      rfl
    rw [← hik]
    exact interior_s_ne_zero_of_relations hq hC hN hcoord k

end ITEMf
