import ITEMf.Construction.Symmetry

/-!
# Explicit ITEM-f rate

This file formalizes the manuscript's half-angle contraction along the finite
shooting orbit and combines it with the two exact endpoint values.
-/

open Set

set_option autoImplicit false

namespace ITEMf

/-- The half-angle cotangent in the form used in the manuscript. -/
noncomputable def halfCot (theta : ℝ) : ℝ :=
  Real.sin theta / (1 - Real.cos theta)

/-- On the open upper semicircle, the manuscript form of the half-angle
cotangent agrees with the usual cosine-over-sine quotient. -/
lemma halfCot_eq_cos_div_sin_half
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    halfCot theta =
      Real.cos (theta / 2) / Real.sin (theta / 2) := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hhalfPos : 0 < theta / 2 :=
    div_pos htheta.1 htwo
  have hhalfLt : theta / 2 < Real.pi := by
    rw [div_lt_iff₀ htwo]
    linarith [htheta.2, Real.pi_pos]
  have hsinPos :
      0 < Real.sin (theta / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalfPos hhalfLt
  have hsin :
      Real.sin theta =
        2 * Real.sin (theta / 2) * Real.cos (theta / 2) := by
    have h := Real.sin_two_mul (theta / 2)
    have harg : 2 * (theta / 2) = theta := by ring
    rwa [harg] at h
  have hcos :
      Real.cos theta =
        1 - 2 * Real.sin (theta / 2) ^ 2 := by
    have hdouble := Real.cos_two_mul (theta / 2)
    have hunit := Real.sin_sq_add_cos_sq (theta / 2)
    have harg : 2 * (theta / 2) = theta := by ring
    rw [harg] at hdouble
    nlinarith
  unfold halfCot
  rw [hsin, hcos]
  field_simp [ne_of_gt hsinPos]
  ring

/-- Algebraic core of the manuscript's strict half-angle contraction. -/
lemma halfCot_contraction
    {r theta phi : ℝ}
    (hr0 : 0 < r) (_hr1 : r < 1)
    (htheta : theta ∈ Ioo (Real.pi / 2) Real.pi)
    (hphi : phi ∈ Ioo (Real.pi / 2) Real.pi)
    (horder : phi < theta)
    (hgap :
      Real.cos (theta - phi) <
        1 - r ^ 2 * (1 + Real.cos phi)) :
    halfCot theta < (1 - r) * halfCot phi := by
  let A := theta / 2
  let B := phi / 2
  let D := (theta - phi) / 2
  have hpi : 0 < Real.pi := Real.pi_pos
  have htwo : (0 : ℝ) < 2 := by norm_num
  have htheta0 : 0 < theta :=
    (div_pos hpi htwo).trans htheta.1
  have hphi0 : 0 < phi :=
    (div_pos hpi htwo).trans hphi.1
  have hA0 : 0 < A := by
    dsimp [A]
    exact div_pos htheta0 htwo
  have hAlt : A < Real.pi / 2 := by
    dsimp [A]
    exact (div_lt_div_iff_of_pos_right htwo).2 htheta.2
  have hB0 : 0 < B := by
    dsimp [B]
    exact div_pos hphi0 htwo
  have hBlt : B < Real.pi / 2 := by
    dsimp [B]
    exact (div_lt_div_iff_of_pos_right htwo).2 hphi.2
  have hD0 : 0 < D := by
    dsimp [D]
    exact div_pos (sub_pos.mpr horder) htwo
  have hDlt : D < Real.pi / 2 := by
    dsimp [D]
    rw [div_lt_div_iff_of_pos_right htwo]
    linarith [htheta.2, hphi0]
  have hsinA : 0 < Real.sin A :=
    Real.sin_pos_of_pos_of_lt_pi hA0 (hAlt.trans (by linarith))
  have hsinB : 0 < Real.sin B :=
    Real.sin_pos_of_pos_of_lt_pi hB0 (hBlt.trans (by linarith))
  have hsinD : 0 < Real.sin D :=
    Real.sin_pos_of_pos_of_lt_pi hD0 (hDlt.trans (by linarith))
  have hcosA : 0 < Real.cos A :=
    Real.cos_pos_of_mem_Ioo (by
      constructor <;> linarith)
  have hcosB : 0 < Real.cos B :=
    Real.cos_pos_of_mem_Ioo (by
      constructor <;> linarith)
  have hsinAlt : Real.sin A < 1 := by
    have hunit := Real.sin_sq_add_cos_sq A
    nlinarith [sq_pos_of_pos hcosA]
  have hcosPhi :
      Real.cos phi = 2 * Real.cos B ^ 2 - 1 := by
    have h := Real.cos_two_mul B
    have harg : 2 * B = phi := by dsimp [B]; ring
    rwa [harg] at h
  have hcosDiff :
      Real.cos (theta - phi) =
        1 - 2 * Real.sin D ^ 2 := by
    have hdouble := Real.cos_two_mul D
    have hunit := Real.sin_sq_add_cos_sq D
    have harg : 2 * D = theta - phi := by dsimp [D]; ring
    rw [harg] at hdouble
    nlinarith
  have hsquare :
      (r * Real.cos B) ^ 2 < Real.sin D ^ 2 := by
    rw [hcosPhi, hcosDiff] at hgap
    nlinarith
  have hstrong :
      r * Real.cos B < Real.sin D := by
    exact
      (sq_lt_sq₀
        (mul_nonneg hr0.le hcosB.le) hsinD.le).mp
        (by simpa [mul_pow] using hsquare)
  have hscaled :
      r * Real.sin A * Real.cos B < Real.sin D := by
    have hlt :
        Real.sin A * (r * Real.cos B) <
          1 * (r * Real.cos B) :=
      mul_lt_mul_of_pos_right hsinAlt (mul_pos hr0 hcosB)
    calc
      r * Real.sin A * Real.cos B =
          Real.sin A * (r * Real.cos B) := by ring
      _ < r * Real.cos B := by simpa using hlt
      _ < Real.sin D := hstrong
  have hsinSub :
      Real.sin D =
        Real.sin A * Real.cos B -
          Real.cos A * Real.sin B := by
    have h := Real.sin_sub A B
    have harg : A - B = D := by dsimp [A, B, D]; ring
    rwa [harg] at h
  rw [halfCot_eq_cos_div_sin_half
      ⟨htheta0, htheta.2⟩,
    halfCot_eq_cos_div_sin_half
      ⟨hphi0, hphi.2⟩]
  dsimp only [A, B] at hsinA hsinB hsinSub hscaled ⊢
  rw [div_lt_iff₀ hsinA]
  have hreassoc :
      (1 - r) *
            (Real.cos (phi / 2) / Real.sin (phi / 2)) *
          Real.sin (theta / 2) =
        ((1 - r) * Real.cos (phi / 2) *
          Real.sin (theta / 2)) /
            Real.sin (phi / 2) := by
    field_simp [ne_of_gt hsinB]
  rw [hreassoc, lt_div_iff₀ hsinB]
  rw [hsinSub] at hscaled
  nlinarith

namespace ValidCoefficients

variable {N : Nat} {q : ℝ} {C : CoeffData N}

/-- The stereographic denominator attached to every interior construction
point is strictly positive. -/
lemma stereoDenom_pos
    (hC : ValidCoefficients q C) (k : Fin N) :
    0 <
      radius C.Upsilon + C.Upsilon -
        C.a (idxInterior k) := by
  have hR : 0 < radius C.Upsilon :=
    radius_pos hC.upsilon_gt_one
  have hratio := (hC.interior_ratio_mem_Ioo k).2
  rw [div_lt_one hR] at hratio
  linarith

/-- The polar-angle half cotangent is the stereographic coordinate used in
the manuscript proof. -/
lemma halfCot_coeffAngle
    (hC : ValidCoefficients q C) (k : Fin N) :
    halfCot (coeffAngle C k) =
      C.b (idxInterior k) /
        (radius C.Upsilon + C.Upsilon -
          C.a (idxInterior k)) := by
  have hR : 0 < radius C.Upsilon :=
    radius_pos hC.upsilon_gt_one
  have hden := hC.stereoDenom_pos k
  have hdenEq :
      1 -
          (C.a (idxInterior k) - C.Upsilon) /
            radius C.Upsilon =
        (radius C.Upsilon + C.Upsilon -
          C.a (idxInterior k)) / radius C.Upsilon := by
    field_simp [ne_of_gt hR]
    ring
  unfold halfCot
  rw [hC.sin_coeffAngle k, hC.cos_coeffAngle k]
  rw [hdenEq]
  field_simp [ne_of_gt hR, ne_of_gt hden]

/-- Every construction angle lies strictly between `pi/2` and `pi`. -/
lemma coeffAngle_mem_piHalf_pi
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) (k : Fin N) :
    coeffAngle C k ∈ Ioo (Real.pi / 2) Real.pi := by
  have hupper := (hC.coeffAngle_mem_Ioo k).2
  have heq := hC.coeffAngle_eq_shootingAngle hN hq k
  have hlower :
      Real.pi / 2 < shootingAngle N q C.Upsilon k := by
    rw [shootingAngle_eq_iter]
    exact
      shootingIter_gt_pi_div_two hq hC.upsilon_gt_one
        (N - 1 - k.1)
  exact ⟨by rwa [heq], hupper⟩

/-- The inner-product recurrence gives the strict half-angle contraction
between consecutive construction angles. -/
lemma halfCot_step
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) (k : Fin (N - 1)) :
    halfCot (coeffAngle C ⟨k.1, by omega⟩) <
      (1 - Real.sqrt q) *
        halfCot (coeffAngle C ⟨k.1 + 1, by omega⟩) := by
  let i : Fin N := ⟨k.1, by omega⟩
  let j : Fin N := ⟨k.1 + 1, by omega⟩
  let theta := coeffAngle C i
  let phi := coeffAngle C j
  let r := Real.sqrt q
  let R := radius C.Upsilon
  have hr0 : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hq.1
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.sqrt_lt' zero_lt_one]
    simpa only [one_pow] using hq.2
  have hr2 : r ^ 2 = q := by
    dsimp [r]
    exact Real.sq_sqrt hq.1.le
  have htheta : theta ∈ Ioo (Real.pi / 2) Real.pi := by
    dsimp [theta, i]
    exact hC.coeffAngle_mem_piHalf_pi hN hq _
  have hphi : phi ∈ Ioo (Real.pi / 2) Real.pi := by
    dsimp [phi, j]
    exact hC.coeffAngle_mem_piHalf_pi hN hq _
  have horder : phi < theta := by
    dsimp [theta, phi, i, j]
    exact hC.coeffAngle_strictAnti (by simp)
  have hp0 : 0 < candidateP q C.Upsilon :=
    candidateP_pos hq hC.upsilon_gt_one
  have hpq : candidateP q C.Upsilon < q :=
    candidateP_lt_q hq hC.upsilon_gt_one
  have harg :
      oneStepArg q (candidateP q C.Upsilon) phi ∈
        Ioo (-1 : ℝ) 1 :=
    oneStepArg_mem_Ioo hq hp0 hpq phi
  have hrec :
      theta =
        oneStep q (candidateP q C.Upsilon) phi := by
    dsimp [theta, phi, i, j]
    exact hC.coeffAngle_recurrence hN hq k
  have hcosGapEq :
      Real.cos (theta - phi) =
        1 - q - candidateP q C.Upsilon * Real.cos phi := by
    rw [hrec]
    unfold oneStep
    simp only [add_sub_cancel_left]
    rw [Real.cos_arccos harg.1.le harg.2.le]
    rfl
  have hratio : R / C.Upsilon < 1 := by
    have hU : 0 < C.Upsilon :=
      zero_lt_one.trans hC.upsilon_gt_one
    apply (div_lt_one hU).2
    dsimp [R]
    exact radius_lt_upsilon hC.upsilon_gt_one
  have hcosNeg : Real.cos phi < 0 := by
    have hupper :
        phi < Real.pi + Real.pi / 2 := by
      linarith [hphi.2, Real.pi_pos]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt hphi.1 hupper
  have hratioCos :
      Real.cos phi < (R / C.Upsilon) * Real.cos phi := by
    have :=
      mul_lt_mul_of_neg_right hratio hcosNeg
    simpa only [one_mul] using this
  have hscaled :
      q * Real.cos phi <
        q * ((R / C.Upsilon) * Real.cos phi) :=
    mul_lt_mul_of_pos_left hratioCos hq.1
  have hp :
      candidateP q C.Upsilon = q * R / C.Upsilon := by
    dsimp [R]
    exact candidateP_eq_q_mul_radius_div hC.upsilon_gt_one
  have hgap :
      Real.cos (theta - phi) <
        1 - r ^ 2 * (1 + Real.cos phi) := by
    rw [hcosGapEq, hp, hr2]
    nlinarith
  have hcontract :=
    halfCot_contraction hr0 hr1 htheta hphi horder hgap
  simpa [theta, phi, i, j, r] using hcontract

/-- Exact half-cotangent values at the first and last construction points. -/
lemma halfCot_endpoints
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hC : ValidCoefficients q C) :
    let first : Fin N := ⟨0, by omega⟩
    let last := lastInteriorIndex N hN
    halfCot (coeffAngle C first) =
        Real.sqrt (1 - q) /
          ((1 - Real.sqrt q) *
            (C.Upsilon + radius C.Upsilon)) ∧
      halfCot (coeffAngle C last) =
        Real.sqrt (1 - q) / (1 + Real.sqrt q) := by
  let first : Fin N := ⟨0, by omega⟩
  let last := lastInteriorIndex N hN
  let aFirst := C.a (idxInterior first)
  let bFirst := C.b (idxInterior first)
  let aLast := C.a (idxInterior last)
  let bLast := C.b (idxInterior last)
  let U := C.Upsilon
  let R := radius U
  let r := Real.sqrt q
  let s := Real.sqrt (1 - q)
  have hU : 0 < U := by
    dsimp [U]
    exact zero_lt_one.trans hC.upsilon_gt_one
  have hR : 0 < R := by
    dsimp [R, U]
    exact radius_pos hC.upsilon_gt_one
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
  have hR2 : R ^ 2 = U ^ 2 - 1 := by
    dsimp [R, U]
    exact radius_sq hC.upsilon_gt_one
  have haLast :
      aLast = U - r * R := by
    have hratio := hC.terminal_ratio hN hq
    dsimp [aLast, U, R, r, last] at hratio ⊢
    field_simp [ne_of_gt
      (radius_pos hC.upsilon_gt_one)] at hratio
    linarith
  have hbLast :
      bLast = s * R := by
    dsimp [bLast, s, R, U, last]
    exact hC.b_lastInterior hN hq
  have hrev :
      reverseIndex (idxInterior first) = idxInterior last := by
    rw [reverseIndex_idxInterior]
    apply congrArg idxInterior
    apply Fin.ext
    simp [first, last, lastInteriorIndex, Fin.rev]
  have hsym :=
    Internal.involutionSymmetry hN hq C hC
      (idxInterior first)
  rw [hrev] at hsym
  have haProduct : aFirst * aLast = 1 := by
    simpa [aFirst, aLast] using hsym.1
  have hbProduct : aFirst * bLast = bFirst := by
    simpa [aFirst, aLast, bFirst, bLast] using hsym.2
  have haLastPos : 0 < aLast := by
    dsimp [aLast]
    exact hC.a_pos _
  have haFirst :
      aFirst = 1 / (U - r * R) := by
    rw [← haLast]
    exact (eq_div_iff (ne_of_gt haLastPos)).2 haProduct
  have hbFirst :
      bFirst = aFirst * (s * R) := by
    rw [← hbLast]
    exact hbProduct.symm
  have hfirstDen :
      0 < R + U - aFirst := by
    dsimp [R, U, aFirst, first]
    exact hC.stereoDenom_pos first
  have hlastDen :
      0 < R + U - aLast := by
    dsimp [R, U, aLast, last]
    exact hC.stereoDenom_pos last
  constructor
  · rw [hC.halfCot_coeffAngle first]
    change
      bFirst / (R + U - aFirst) =
        s / ((1 - r) * (U + R))
    rw [hbFirst, haFirst]
    have hUrR : 0 < U - r * R := by
      rw [← haLast]
      exact haLastPos
    have htargetDen :
        0 < (1 - r) * (U + R) :=
      mul_pos (sub_pos.mpr hrlt) (add_pos hU hR)
    have hcombined :
        (U - r * R) * (R + U) - 1 =
          R * (1 - r) * (U + R) := by
      nlinarith
    have hcombinedPos :
        0 < (U - r * R) * (R + U) - 1 := by
      rw [hcombined]
      positivity
    have hrawDen :
        R + U - 1 / (U - r * R) =
          ((U - r * R) * (R + U) - 1) /
            (U - r * R) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        R + U - 1 * (U - r * R)⁻¹ =
            (R + U) *
                ((U - r * R) * (U - r * R)⁻¹) -
              (U - r * R)⁻¹ := by
                rw [mul_inv_cancel₀ (ne_of_gt hUrR)]
                ring
        _ =
            ((U - r * R) * (R + U) - 1) *
              (U - r * R)⁻¹ := by ring
    rw [hrawDen]
    calc
      (1 / (U - r * R) * (s * R)) /
            (((U - r * R) * (R + U) - 1) /
              (U - r * R)) =
          s * R / ((U - r * R) * (R + U) - 1) := by
            field_simp [ne_of_gt hUrR, ne_of_gt hcombinedPos]
      _ = s / ((1 - r) * (U + R)) := by
            rw [hcombined]
            field_simp [ne_of_gt hR, ne_of_gt htargetDen]
  · rw [hC.halfCot_coeffAngle last]
    change
      bLast / (R + U - aLast) = s / (1 + r)
    rw [hbLast, haLast]
    have hden : 0 < 1 + r := by linarith
    have htermDen :
        R + U - (U - r * R) = R * (1 + r) := by
      ring
    rw [htermDen]
    field_simp [ne_of_gt hR, ne_of_gt hden]

end ValidCoefficients

namespace Internal

/-- The exact finite half-angle chain gives the explicit manuscript
relaxation `Upsilon⁻² < 4 (1 - sqrt q)^(2N)`. -/
theorem explicitRate
    {N : Nat} {q : ℝ} (hN : 1 ≤ N) (hq : UnitRatio q)
    (C : CoeffData N) (hC : ValidCoefficients q C) :
    ExplicitRateResult q C := by
  let first : Fin N := ⟨0, by omega⟩
  let last := lastInteriorIndex N hN
  let U := C.Upsilon
  let R := radius U
  let r := Real.sqrt q
  let s := Real.sqrt (1 - q)
  let c := 1 - r
  have hU : 0 < U := by
    dsimp [U]
    exact zero_lt_one.trans hC.upsilon_gt_one
  have hR : 0 < R := by
    dsimp [R, U]
    exact radius_pos hC.upsilon_gt_one
  have hRltU : R < U := by
    dsimp [R, U]
    exact radius_lt_upsilon hC.upsilon_gt_one
  have hr : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hq.1
  have hrlt : r < 1 := by
    dsimp [r]
    rw [Real.sqrt_lt' zero_lt_one]
    simpa only [one_pow] using hq.2
  have hc : 0 < c := by
    dsimp [c]
    linarith
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by linarith [hq.2])
  have hr2 : r ^ 2 = q := by
    dsimp [r]
    exact Real.sq_sqrt hq.1.le
  have hs2 : s ^ 2 = 1 - q := by
    dsimp [s]
    exact Real.sq_sqrt (by linarith [hq.2])
  have hend := hC.halfCot_endpoints hN hq
  dsimp only at hend
  have hchain :
      ∀ m : Nat, ∀ hm : m < N,
        halfCot (coeffAngle C first) ≤
          c ^ m *
            halfCot (coeffAngle C (⟨m, hm⟩ : Fin N)) := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hidx :
            (⟨0, hm⟩ : Fin N) = first := by
          apply Fin.ext
          rfl
        simp [hidx]
    | succ m ih =>
        intro hsucc
        have hm : m < N := by omega
        have hk : m < N - 1 := by omega
        let k : Fin (N - 1) := ⟨m, hk⟩
        have hstep := hC.halfCot_step hN hq k
        have hstep' :
            halfCot (coeffAngle C (⟨m, hm⟩ : Fin N)) <
              c *
                halfCot
                  (coeffAngle C
                    (⟨m + 1, hsucc⟩ : Fin N)) := by
          simpa [k, c] using hstep
        have hpow : 0 < c ^ m := pow_pos hc m
        exact (calc
          halfCot (coeffAngle C first) ≤
              c ^ m *
                halfCot
                  (coeffAngle C (⟨m, hm⟩ : Fin N)) :=
            ih hm
          _ < c ^ m *
                (c *
                  halfCot
                    (coeffAngle C
                      (⟨m + 1, hsucc⟩ : Fin N))) :=
            mul_lt_mul_of_pos_left hstep' hpow
          _ = c ^ (m + 1) *
                halfCot
                  (coeffAngle C
                    (⟨m + 1, hsucc⟩ : Fin N)) := by
            rw [pow_succ]
            ring).le
  have hNm1 : N - 1 < N := by omega
  have hlastIndex :
      (⟨N - 1, hNm1⟩ : Fin N) = last := by
    apply Fin.ext
    simp [last, lastInteriorIndex]
  have hchainLast :=
    hchain (N - 1) hNm1
  rw [hlastIndex] at hchainLast
  have hlastPos :
      0 < halfCot (coeffAngle C last) := by
    rw [hend.2]
    exact div_pos hs (by linarith)
  have hproduct :
      halfCot (coeffAngle C first) *
          halfCot (coeffAngle C last) =
        1 / (U + R) := by
    rw [hend.1, hend.2]
    have hcne : c ≠ 0 := ne_of_gt hc
    have hsum : 0 < U + R := add_pos hU hR
    have hrden : 0 < 1 + r := by linarith
    change
      (s / (c * (U + R))) * (s / (1 + r)) =
        1 / (U + R)
    field_simp [hcne, ne_of_gt hsum, ne_of_gt hrden]
    dsimp [c] at *
    nlinarith
  have hlastSq :
      halfCot (coeffAngle C last) ^ 2 =
        c / (1 + r) := by
    rw [hend.2]
    have hrden : 0 < 1 + r := by linarith
    change (s / (1 + r)) ^ 2 = c / (1 + r)
    field_simp [ne_of_gt hrden]
    dsimp [c] at *
    nlinarith
  have hlastSqLt :
      halfCot (coeffAngle C last) ^ 2 < c := by
    rw [hlastSq]
    have hrden : 0 < 1 + r := by linarith
    rw [div_lt_iff₀ hrden]
    nlinarith
  have hmul :=
    mul_le_mul_of_nonneg_right hchainLast hlastPos.le
  have hpowPos : 0 < c ^ (N - 1) :=
    pow_pos hc _
  have hstrict :
      c ^ (N - 1) *
          halfCot (coeffAngle C last) ^ 2 <
        c ^ (N - 1) * c :=
    mul_lt_mul_of_pos_left hlastSqLt hpowPos
  have htoPower :
      1 / (U + R) < c ^ N := by
    have hNdecomp : N = (N - 1) + 1 := by omega
    rw [hproduct] at hmul
    have hmul' :
        1 / (U + R) ≤
          c ^ (N - 1) *
            halfCot (coeffAngle C last) ^ 2 := by
      nlinarith [hmul]
    calc
      1 / (U + R) ≤
          c ^ (N - 1) *
            halfCot (coeffAngle C last) ^ 2 := hmul'
      _ < c ^ (N - 1) * c := hstrict
      _ = c ^ N := by
        rw [← pow_succ, ← hNdecomp]
  have hdenOrder : U + R < 2 * U := by
    linarith
  have hhalf :
      1 / (2 * U) < c ^ N := by
    have hinv :
        1 / (2 * U) < 1 / (U + R) :=
      one_div_lt_one_div_of_lt (add_pos hU hR) hdenOrder
    exact hinv.trans htoPower
  have hInv :
      1 / U < 2 * c ^ N := by
    have htwo : (0 : ℝ) < 2 := by norm_num
    have hmul2 :=
      mul_lt_mul_of_pos_left hhalf htwo
    have hleft :
        2 * (1 / (2 * U)) = 1 / U := by
      field_simp [ne_of_gt hU]
    rwa [hleft] at hmul2
  have hsquare :
      (1 / U) ^ 2 < (2 * c ^ N) ^ 2 := by
    exact
      (sq_lt_sq₀
        (one_div_nonneg.mpr hU.le)
        (mul_nonneg (by norm_num) (pow_nonneg hc.le N))).2
        hInv
  have hleft :
      1 / U ^ 2 = (1 / U) ^ 2 := by
    field_simp [ne_of_gt hU]
  have hright :
      4 * c ^ (2 * N) = (2 * c ^ N) ^ 2 := by
    calc
      4 * c ^ (2 * N) = 4 * c ^ (N * 2) := by
        rw [Nat.mul_comm 2 N]
      _ = 4 * (c ^ N) ^ 2 := by
        rw [pow_mul]
      _ = (2 * c ^ N) ^ 2 := by ring
  change 1 / U ^ 2 < 4 * c ^ (2 * N)
  rw [hleft, hright]
  exact hsquare

end Internal


end ITEMf
