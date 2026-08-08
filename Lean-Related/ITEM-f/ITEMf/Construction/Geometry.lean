import ITEMf.Construction.Orbit

/-!
# Circle coordinates and candidate configurations

This module provides the exact polar-coordinate bridge between the finite
`CoeffData` specification and the backward shooting angles.
-/

open Set

set_option autoImplicit false

namespace ITEMf

@[ext] theorem CoeffData.ext
    {N : Nat} {C C' : CoeffData N}
    (hUpsilon : C.Upsilon = C'.Upsilon)
    (ha : C.a = C'.a) (hb : C.b = C'.b) :
    C = C' := by
  cases C
  cases C'
  simp_all

/-- Candidate first coordinate, indexed by the manuscript index. -/
noncomputable def candidateA
    (N : Nat) (q Upsilon : ℝ) (i : Fin (N + 2)) : ℝ :=
  if i.1 = 0 then
    1 / Upsilon
  else if i.1 = N + 1 then
    Upsilon
  else
    Upsilon + radius Upsilon *
      Real.cos (shootingIter q Upsilon (N - i.1))

/-- Candidate second coordinate, indexed by the manuscript index. -/
noncomputable def candidateB
    (N : Nat) (q Upsilon : ℝ) (i : Fin (N + 2)) : ℝ :=
  if i.1 = 0 then
    Real.sqrt (1 - q) * radius Upsilon / Upsilon
  else if i.1 = N + 1 then
    Real.sqrt (1 - q) * radius Upsilon
  else
    radius Upsilon *
      Real.sin (shootingIter q Upsilon (N - i.1))

/-- The complete candidate coefficient table at a fixed shooting parameter. -/
noncomputable def candidateData
    (N : Nat) (q Upsilon : ℝ) : CoeffData N where
  Upsilon := Upsilon
  a := candidateA N q Upsilon
  b := candidateB N q Upsilon

@[simp] lemma candidateData_upsilon
    (N : Nat) (q Upsilon : ℝ) :
    (candidateData N q Upsilon).Upsilon = Upsilon := rfl

@[simp] lemma candidateA_zero
    (N : Nat) (q Upsilon : ℝ) :
    candidateA N q Upsilon (idxZero N) = 1 / Upsilon := by
  simp [candidateA, idxZero]

@[simp] lemma candidateB_zero
    (N : Nat) (q Upsilon : ℝ) :
    candidateB N q Upsilon (idxZero N) =
      Real.sqrt (1 - q) * radius Upsilon / Upsilon := by
  simp [candidateB, idxZero]

@[simp] lemma candidateA_last
    (N : Nat) (q Upsilon : ℝ) :
    candidateA N q Upsilon (idxLast N) = Upsilon := by
  simp [candidateA, idxLast]

@[simp] lemma candidateB_last
    (N : Nat) (q Upsilon : ℝ) :
    candidateB N q Upsilon (idxLast N) =
      Real.sqrt (1 - q) * radius Upsilon := by
  simp [candidateB, idxLast]

@[simp] lemma candidateA_interior
    {N : Nat} (q Upsilon : ℝ) (k : Fin N) :
    candidateA N q Upsilon (idxInterior k) =
      Upsilon + radius Upsilon *
        Real.cos (shootingAngle N q Upsilon k) := by
  have hk : k.1 ≠ N := by omega
  have hklt : k.1 < N := k.2
  have hexp : N - (k.1 + 1) = N - 1 - k.1 := by omega
  simp [candidateA, idxInterior, shootingAngle, shootingIter, hk, hexp]

@[simp] lemma candidateB_interior
    {N : Nat} (q Upsilon : ℝ) (k : Fin N) :
    candidateB N q Upsilon (idxInterior k) =
      radius Upsilon *
        Real.sin (shootingAngle N q Upsilon k) := by
  have hk : k.1 ≠ N := by omega
  have hklt : k.1 < N := k.2
  have hexp : N - (k.1 + 1) = N - 1 - k.1 := by omega
  simp [candidateB, idxInterior, shootingAngle, shootingIter, hk, hexp]

/-- The polar angle of an interior point in a valid configuration. -/
noncomputable def coeffAngle
    {N : Nat} (C : CoeffData N) (k : Fin N) : ℝ :=
  Real.arccos
    ((C.a (idxInterior k) - C.Upsilon) / radius C.Upsilon)

lemma cos_targetAngleValue
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    Real.cos (targetAngleValue q Upsilon) = targetCos q Upsilon := by
  unfold targetAngleValue
  have hmem := targetCos_mem_Ioo hq hUpsilon
  exact Real.cos_arccos hmem.1.le hmem.2.le

/-- The abscissa of the farther target intersection, in its rational form. -/
lemma targetAbscissa_eq
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    Upsilon + radius Upsilon * Real.cos (targetAngleValue q Upsilon) =
      (Upsilon + Real.sqrt q * radius Upsilon) /
        (q + (1 - q) * Upsilon ^ 2) := by
  have hDne : q + (1 - q) * Upsilon ^ 2 ≠ 0 :=
    ne_of_gt (targetDenom_pos hq hUpsilon)
  have hDne' : q + Upsilon ^ 2 * (1 - q) ≠ 0 := by
    simpa only [mul_comm] using hDne
  have hR2 : radius Upsilon ^ 2 = Upsilon ^ 2 - 1 :=
    radius_sq hUpsilon
  rw [cos_targetAngleValue hq hUpsilon]
  unfold targetCos
  field_simp [hDne, hDne']
  ring_nf
  rw [hR2]
  ring

lemma inv_lt_targetAbscissa
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    1 / Upsilon <
      Upsilon + radius Upsilon * Real.cos (targetAngleValue q Upsilon) := by
  have hU : 0 < Upsilon := zero_lt_one.trans hUpsilon
  have hD : 0 < q + (1 - q) * Upsilon ^ 2 :=
    targetDenom_pos hq hUpsilon
  have hR : 0 < radius Upsilon := radius_pos hUpsilon
  have hr : 0 < Real.sqrt q := Real.sqrt_pos.2 hq.1
  have hr2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.1.le
  have hR2 : radius Upsilon ^ 2 = Upsilon ^ 2 - 1 :=
    radius_sq hUpsilon
  rw [targetAbscissa_eq hq hUpsilon]
  rw [div_lt_div_iff₀ hU hD]
  nlinarith [mul_pos hr hR]

/-- The farther target point lies on the endpoint line through the origin. -/
lemma targetAngle_line
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    Real.sin (targetAngleValue q Upsilon) =
      Real.sqrt (1 - q) *
        (Upsilon +
          radius Upsilon * Real.cos (targetAngleValue q Upsilon)) := by
  let R := radius Upsilon
  let r := Real.sqrt q
  let s := Real.sqrt (1 - q)
  let D := q + (1 - q) * Upsilon ^ 2
  let c := targetCos q Upsilon
  let a := Upsilon + R * c
  have hR : 0 < R := by
    dsimp [R]
    exact radius_pos hUpsilon
  have hr : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hq.1
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by linarith [hq.2])
  have hD : 0 < D := by
    dsimp [D]
    exact targetDenom_pos hq hUpsilon
  have hr2 : r ^ 2 = q := by
    dsimp [r]
    exact Real.sq_sqrt hq.1.le
  have hs2 : s ^ 2 = 1 - q := by
    dsimp [s]
    exact Real.sq_sqrt (by linarith [hq.2])
  have hR2 : R ^ 2 = Upsilon ^ 2 - 1 := by
    dsimp [R]
    exact radius_sq hUpsilon
  have hc :
      c = (r - (1 - q) * R * Upsilon) / D := by
    rfl
  have ha :
      a = (Upsilon + r * R) / D := by
    dsimp [a]
    rw [hc]
    field_simp [ne_of_gt hD]
    nlinarith
  have haPos : 0 < a := by
    rw [ha]
    exact div_pos (add_pos (zero_lt_one.trans hUpsilon) (mul_pos hr hR)) hD
  have hunit : 1 - c ^ 2 = (s * a) ^ 2 := by
    rw [hc, ha]
    field_simp [ne_of_gt hD]
    dsimp [D]
    ring_nf
    rw [hr2, hs2, hR2]
    ring
  have hsin :
      Real.sin (targetAngleValue q Upsilon) =
        Real.sqrt (1 - c ^ 2) := by
    unfold targetAngleValue
    rw [Real.sin_arccos]
  have hsqrtSq :
      Real.sqrt (1 - c ^ 2) ^ 2 = 1 - c ^ 2 := by
    have hcMem : c ∈ Ioo (-1 : ℝ) 1 := by
      simpa only [c] using targetCos_mem_Ioo hq hUpsilon
    rcases hcMem with ⟨hcLower, hcUpper⟩
    apply Real.sq_sqrt
    nlinarith [mul_pos (by linarith : 0 < 1 - c)
      (by linarith : 0 < 1 + c)]
  have heq : Real.sqrt (1 - c ^ 2) = s * a := by
    have hsqrt0 : 0 ≤ Real.sqrt (1 - c ^ 2) := Real.sqrt_nonneg _
    have hsa : 0 < s * a := mul_pos hs haPos
    nlinarith
  rw [cos_targetAngleValue hq hUpsilon]
  change Real.sin (targetAngleValue q Upsilon) = s * a
  rw [hsin, heq]

namespace ValidCoefficients

variable {N : Nat} {q : ℝ} {C : CoeffData N}

lemma interior_ratio_mem_Ioo
    (hC : ValidCoefficients q C) (k : Fin N) :
    (C.a (idxInterior k) - C.Upsilon) / radius C.Upsilon ∈
      Ioo (-1 : ℝ) 1 := by
  let x := C.a (idxInterior k) - C.Upsilon
  let y := C.b (idxInterior k)
  let R := radius C.Upsilon
  have hR : 0 < R := by
    dsimp [R]
    exact radius_pos hC.upsilon_gt_one
  have hy : 0 < y := by
    dsimp [y]
    exact hC.b_pos _
  have hcircle : x ^ 2 + y ^ 2 = R ^ 2 := by
    dsimp [x, y, R]
    rw [hC.circle k, radius_sq hC.upsilon_gt_one]
  have hxsq : x ^ 2 < R ^ 2 := by
    nlinarith [sq_pos_of_pos hy]
  have hxLower : -R < x := by
    nlinarith [sq_nonneg (x - R)]
  have hxUpper : x < R := by
    nlinarith [sq_nonneg (x + R)]
  change x / R ∈ Ioo (-1 : ℝ) 1
  constructor
  · rw [lt_div_iff₀ hR]
    simpa only [neg_mul, one_mul] using hxLower
  · rw [div_lt_iff₀ hR]
    simpa only [one_mul] using hxUpper

lemma coeffAngle_mem_Ioo
    (hC : ValidCoefficients q C) (k : Fin N) :
    coeffAngle C k ∈ Ioo (0 : ℝ) Real.pi := by
  have hratio := hC.interior_ratio_mem_Ioo k
  unfold coeffAngle
  exact ⟨Real.arccos_pos.mpr hratio.2,
    Real.arccos_lt_pi.mpr hratio.1⟩

lemma cos_coeffAngle
    (hC : ValidCoefficients q C) (k : Fin N) :
    Real.cos (coeffAngle C k) =
      (C.a (idxInterior k) - C.Upsilon) / radius C.Upsilon := by
  have hratio := hC.interior_ratio_mem_Ioo k
  unfold coeffAngle
  exact Real.cos_arccos hratio.1.le hratio.2.le

lemma a_eq_polar
    (hC : ValidCoefficients q C) (k : Fin N) :
    C.a (idxInterior k) =
      C.Upsilon + radius C.Upsilon * Real.cos (coeffAngle C k) := by
  have hRne : radius C.Upsilon ≠ 0 :=
    ne_of_gt (radius_pos hC.upsilon_gt_one)
  rw [hC.cos_coeffAngle k]
  field_simp
  ring

lemma sin_coeffAngle
    (hC : ValidCoefficients q C) (k : Fin N) :
    Real.sin (coeffAngle C k) =
      C.b (idxInterior k) / radius C.Upsilon := by
  let x := (C.a (idxInterior k) - C.Upsilon) / radius C.Upsilon
  let z := C.b (idxInterior k) / radius C.Upsilon
  have hR : 0 < radius C.Upsilon := radius_pos hC.upsilon_gt_one
  have hz : 0 < z := by
    dsimp [z]
    exact div_pos (hC.b_pos _) hR
  have hx := hC.interior_ratio_mem_Ioo k
  have hrad : 0 < 1 - x ^ 2 := by
    have hxLower : -1 < x := by simpa only [x] using hx.1
    have hxUpper : x < 1 := by simpa only [x] using hx.2
    nlinarith [mul_pos (by linarith : 0 < 1 - x)
      (by linarith : 0 < 1 + x)]
  have hsqrtSq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hrad.le
  have hzSq : z ^ 2 = 1 - x ^ 2 := by
    have hcircle := hC.circle k
    have hRne : radius C.Upsilon ≠ 0 := ne_of_gt hR
    dsimp [x, z]
    rw [← radius_sq hC.upsilon_gt_one] at hcircle
    field_simp [hRne]
    nlinarith
  have heq : Real.sqrt (1 - x ^ 2) = z := by
    have hsqrt0 : 0 ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_nonneg _
    nlinarith
  unfold coeffAngle
  rw [Real.sin_arccos]
  exact heq

lemma b_eq_polar
    (hC : ValidCoefficients q C) (k : Fin N) :
    C.b (idxInterior k) =
      radius C.Upsilon * Real.sin (coeffAngle C k) := by
  rw [hC.sin_coeffAngle k]
  field_simp [ne_of_gt (radius_pos hC.upsilon_gt_one)]

lemma coeffAngle_strictAnti
    (hC : ValidCoefficients q C) {i j : Fin N} (hij : i.1 < j.1) :
    coeffAngle C j < coeffAngle C i := by
  have ha :
      C.a (idxInterior i) < C.a (idxInterior j) :=
    hC.a_strict (by simp [idxInterior, hij])
  have hR : 0 < radius C.Upsilon := radius_pos hC.upsilon_gt_one
  have hratio :
      (C.a (idxInterior i) - C.Upsilon) / radius C.Upsilon <
        (C.a (idxInterior j) - C.Upsilon) / radius C.Upsilon := by
    exact div_lt_div_of_pos_right (by linarith) hR
  have hi := hC.interior_ratio_mem_Ioo i
  have hj := hC.interior_ratio_mem_Ioo j
  unfold coeffAngle
  exact Real.arccos_lt_arccos hi.1.le hratio hj.2.le

end ValidCoefficients
end ITEMf
