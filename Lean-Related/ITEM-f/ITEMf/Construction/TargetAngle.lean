import ITEMf.Construction.Domain

/-!
# The ITEM-f target angle

The key point is the corrected derivative from AR031.  It replaces the
informally invalid quotient-monotonicity sentence in the earlier manuscript
draft and proves strict increase of the target angle.
-/

open Set Filter

set_option autoImplicit false

namespace ITEMf

lemma targetDenom_pos
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    0 < q + (1 - q) * Upsilon ^ 2 := by
  have hA : 0 < 1 - q := by linarith [hq.2]
  have hUpos : 0 < Upsilon := lt_trans zero_lt_one hUpsilon
  have hU2 : 0 < Upsilon ^ 2 := sq_pos_of_pos hUpos
  exact add_pos hq.1 (mul_pos hA hU2)

lemma targetCos_mem_Ioo
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    targetCos q Upsilon ∈ Ioo (-1 : ℝ) 1 := by
  let r := Real.sqrt q
  let R := radius Upsilon
  let A := 1 - q
  let D := q + A * Upsilon ^ 2
  have hq0 : 0 < q := hq.1
  have hq1 : q < 1 := hq.2
  have hr0 : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hq0
  have hrlt : r < 1 := by
    dsimp [r]
    rw [Real.sqrt_lt' zero_lt_one]
    simpa only [one_pow] using hq1
  have hA : 0 < A := by dsimp [A]; linarith
  have hUpos : 0 < Upsilon := lt_trans zero_lt_one hUpsilon
  have hRpos : 0 < R := by
    dsimp [R]
    exact radius_pos hUpsilon
  have hRlt : R < Upsilon := by
    dsimp [R]
    exact radius_lt_upsilon hUpsilon
  have hD : 0 < D := by
    dsimp [D, A]
    exact targetDenom_pos hq hUpsilon
  have hDone : 1 < D := by
    dsimp [D, A]
    nlinarith [mul_pos hA
      (mul_pos (sub_pos.mpr hUpsilon) (add_pos hUpos zero_lt_one))]
  have hnumlt : r - A * R * Upsilon < D := by
    have hprod : 0 < A * R * Upsilon := by positivity
    linarith
  have hnumplus : 0 < (r - A * R * Upsilon) + D := by
    have hgap : 0 < Upsilon - R := by linarith
    have hpositive : 0 < A * Upsilon * (Upsilon - R) := by positivity
    dsimp [D]
    nlinarith
  change
    (r - A * R * Upsilon) / D ∈ Ioo (-1 : ℝ) 1
  constructor
  · rw [lt_div_iff₀ hD]
    nlinarith
  · rw [div_lt_iff₀ hD]
    simpa only [one_mul] using hnumlt

lemma targetCos_continuousOn {q : ℝ} (hq : UnitRatio q) :
    ContinuousOn (targetCos q) (Ioi (1 : ℝ)) := by
  have hR : ContinuousOn radius (Ioi (1 : ℝ)) := by
    unfold radius
    fun_prop
  have hnum :
      ContinuousOn
        (fun U : ℝ =>
          Real.sqrt q - (1 - q) * radius U * U) (Ioi (1 : ℝ)) :=
    continuousOn_const.sub ((continuousOn_const.mul hR).mul continuousOn_id)
  have hden :
      ContinuousOn
        (fun U : ℝ => q + (1 - q) * U ^ 2) (Ioi (1 : ℝ)) :=
    continuousOn_const.add (continuousOn_const.mul (continuousOn_id.pow 2))
  unfold targetCos
  exact hnum.div hden
    (fun U hU => ne_of_gt (targetDenom_pos hq hU))

lemma targetCosDerivative_eq_quotient
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    targetCosDerivative q Upsilon =
      ((-(1 - q) *
            ((Upsilon / radius Upsilon) * Upsilon + radius Upsilon)) *
          (q + (1 - q) * Upsilon ^ 2) -
        (Real.sqrt q - (1 - q) * radius Upsilon * Upsilon) *
          ((1 - q) * (2 * Upsilon))) /
        (q + (1 - q) * Upsilon ^ 2) ^ 2 := by
  have hRne : radius Upsilon ≠ 0 :=
    ne_of_gt (radius_pos hUpsilon)
  have hDne : q + (1 - q) * Upsilon ^ 2 ≠ 0 :=
    ne_of_gt (targetDenom_pos hq hUpsilon)
  have hR2 : radius Upsilon ^ 2 = Upsilon ^ 2 - 1 := by
    simpa [radiusSq] using radius_sq hUpsilon
  have hfactor :
      (Upsilon ^ 2 + radius Upsilon ^ 2) *
            (q + (1 - q) * Upsilon ^ 2) -
          2 * (1 - q) * Upsilon ^ 2 * radius Upsilon ^ 2 -
          ((1 + q) * Upsilon ^ 2 - q) =
        (radius Upsilon ^ 2 - Upsilon ^ 2 + 1) *
          (Upsilon ^ 2 * q - Upsilon ^ 2 + q) := by
    ring
  have hcore :
      (Upsilon ^ 2 + radius Upsilon ^ 2) *
            (q + (1 - q) * Upsilon ^ 2) +
          2 * Upsilon * radius Upsilon *
            (Real.sqrt q -
              (1 - q) * radius Upsilon * Upsilon) =
        (1 + q) * Upsilon ^ 2 - q +
          2 * Real.sqrt q * Upsilon * radius Upsilon := by
    have hzero :
        radius Upsilon ^ 2 - Upsilon ^ 2 + 1 = 0 := by
      nlinarith
    rw [hzero, zero_mul] at hfactor
    nlinarith
  unfold targetCosDerivative
  field_simp [hRne, hDne]
  have hscaled :=
    congrArg (fun x : ℝ => -(1 - q) * x) hcore
  ring_nf at hscaled ⊢
  exact hscaled.symm

lemma targetCos_hasDerivAt
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    HasDerivAt (targetCos q) (targetCosDerivative q Upsilon) Upsilon := by
  let r := Real.sqrt q
  let R := radius Upsilon
  let A := 1 - q
  let D := q + A * Upsilon ^ 2
  have hRpos : 0 < R := by
    dsimp [R]
    exact radius_pos hUpsilon
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hDpos : 0 < D := by
    dsimp [D, A]
    exact targetDenom_pos hq hUpsilon
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hRderiv :
      HasDerivAt radius (Upsilon / R) Upsilon := by
    simpa only [R] using radius_hasDerivAt hUpsilon
  have hnum :
      HasDerivAt
        (fun U : ℝ => Real.sqrt q - (1 - q) * radius U * U)
        (-A * ((Upsilon / R) * Upsilon + R)) Upsilon := by
    have hprod :=
      ((hRderiv.const_mul (1 - q)).mul (hasDerivAt_id' Upsilon))
    have hsub := (hasDerivAt_const Upsilon (Real.sqrt q)).sub hprod
    have hsub' :
        HasDerivAt
          (fun U : ℝ => Real.sqrt q - (1 - q) * radius U * U)
          (-((1 - q) * (Upsilon / R) * Upsilon +
            (1 - q) * radius Upsilon)) Upsilon := by
      simpa only [Pi.sub_apply, Pi.mul_apply, id_eq, zero_sub, mul_one] using!
        hsub
    convert hsub' using 1
    dsimp [A]
    ring
  have hden :
      HasDerivAt
        (fun U : ℝ => q + (1 - q) * U ^ 2)
        (A * (2 * Upsilon)) Upsilon := by
    have hpow := (hasDerivAt_id' Upsilon).pow 2
    have hmul := hpow.const_mul (1 - q)
    have hadd := (hasDerivAt_const Upsilon q).add hmul
    have hadd' :
        HasDerivAt
          (fun U : ℝ => q + (1 - q) * U ^ 2)
          ((1 - q) * (2 * Upsilon)) Upsilon := by
      simpa only [Pi.add_apply, Pi.pow_apply, id_eq, zero_add,
        Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using! hadd
    simpa only [A] using hadd'
  have hquot := hnum.div hden hDne
  have hquot' :
      HasDerivAt (targetCos q)
        (((-A * ((Upsilon / R) * Upsilon + R)) * D -
            (r - A * R * Upsilon) * (A * (2 * Upsilon))) /
          D ^ 2) Upsilon := by
    change
      HasDerivAt
        (fun U : ℝ =>
          (Real.sqrt q - (1 - q) * radius U * U) /
            (q + (1 - q) * U ^ 2))
        (((-A * ((Upsilon / R) * Upsilon + R)) * D -
            (r - A * R * Upsilon) * (A * (2 * Upsilon))) /
          D ^ 2) Upsilon
    simpa [r, A, D] using! hquot
  rw [targetCosDerivative_eq_quotient hq hUpsilon]
  simpa [r, R, A, D] using hquot'

lemma targetCos_derivative_neg
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    targetCosDerivative q Upsilon < 0 := by
  have hA : 0 < 1 - q := by linarith [hq.2]
  have hR : 0 < radius Upsilon := radius_pos hUpsilon
  have hD : 0 < q + (1 - q) * Upsilon ^ 2 :=
    targetDenom_pos hq hUpsilon
  have hUpos : 0 < Upsilon := lt_trans zero_lt_one hUpsilon
  have hr : 0 < Real.sqrt q := Real.sqrt_pos.2 hq.1
  have hbracket :
      0 <
        (1 + q) * Upsilon ^ 2 - q +
          2 * Real.sqrt q * Upsilon * radius Upsilon := by
    have hqnonneg : 0 ≤ q := hq.1.le
    have hterm : 0 ≤ 2 * Real.sqrt q * Upsilon * radius Upsilon := by positivity
    nlinarith [mul_pos (by linarith : 0 < 1 + q)
      (mul_pos (sub_pos.mpr hUpsilon) (add_pos hUpos zero_lt_one))]
  unfold targetCosDerivative
  have hden :
      0 <
        radius Upsilon *
          (q + (1 - q) * Upsilon ^ 2) ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hA hbracket)) hden

lemma targetCos_strictAntiOn
    {q : ℝ} (hq : UnitRatio q) :
    StrictAntiOn (targetCos q) (Ioi (1 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (1 : ℝ))
    (targetCos_continuousOn hq)
  intro U hU
  have hU' : 1 < U := by simpa using hU
  rw [(targetCos_hasDerivAt hq hU').deriv]
  exact targetCos_derivative_neg hq hU'

lemma targetAngle_range
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    targetAngleValue q Upsilon ∈ Ioo (0 : ℝ) Real.pi := by
  have hcos := targetCos_mem_Ioo hq hUpsilon
  unfold targetAngleValue
  exact ⟨Real.arccos_pos.mpr hcos.2, Real.arccos_lt_pi.mpr hcos.1⟩

lemma targetAngle_continuousOn {q : ℝ} (hq : UnitRatio q) :
    ContinuousOn (targetAngleValue q) (Ioi (1 : ℝ)) := by
  unfold targetAngleValue
  exact (targetCos_continuousOn hq).arccos

lemma targetAngle_strictMonoOn
    {q : ℝ} (hq : UnitRatio q) :
    StrictMonoOn (targetAngleValue q) (Ioi (1 : ℝ)) := by
  intro U hU V hV hUV
  have hanti := targetCos_strictAntiOn hq hU hV hUV
  have hmemU := targetCos_mem_Ioo hq hU
  have hmemV := targetCos_mem_Ioo hq hV
  unfold targetAngleValue
  exact Real.arccos_lt_arccos hmemV.1.le hanti hmemU.2.le

lemma targetCos_tendsto_one
    {q : ℝ} (hq : UnitRatio q) :
    Tendsto (targetCos q) (nhdsWithin (1 : ℝ) (Ioi 1))
      (nhds (Real.sqrt q)) := by
  let l := nhdsWithin (1 : ℝ) (Ioi 1)
  have hU : Tendsto (fun U : ℝ => U) l (nhds 1) :=
    tendsto_id.mono_left inf_le_left
  have hR : Tendsto radius l (nhds 0) := radius_tendsto_one
  have hnum :
      Tendsto
        (fun U : ℝ =>
          Real.sqrt q - (1 - q) * radius U * U) l
        (nhds (Real.sqrt q)) := by
    convert tendsto_const_nhds.sub
      ((tendsto_const_nhds.mul hR).mul hU) using 1 <;> ring
  have hden :
      Tendsto
        (fun U : ℝ => q + (1 - q) * U ^ 2) l
        (nhds 1) := by
    convert tendsto_const_nhds.add
      (tendsto_const_nhds.mul (hU.pow 2)) using 1 <;> ring
  have hquot := hnum.div hden one_ne_zero
  unfold targetCos
  have heq :
      ((fun U : ℝ => Real.sqrt q - (1 - q) * radius U * U) /
          fun U : ℝ => q + (1 - q) * U ^ 2) =ᶠ[l]
        (fun U : ℝ =>
          (Real.sqrt q - (1 - q) * radius U * U) /
            (q + (1 - q) * U ^ 2)) := by
    filter_upwards with U
    rfl
  simpa only [div_one] using hquot.congr' heq

lemma targetAngle_tendsto_one
    {q : ℝ} (hq : UnitRatio q) :
    Tendsto (targetAngleValue q) (nhdsWithin (1 : ℝ) (Ioi 1))
      (nhds (Real.arccos (Real.sqrt q))) := by
  have h :=
    Real.continuous_arccos.continuousAt.tendsto.comp
      (targetCos_tendsto_one hq)
  unfold targetAngleValue
  exact h

lemma targetCos_tendsto_atTop
    {q : ℝ} (hq : UnitRatio q) :
    Tendsto (targetCos q) atTop (nhds (-1 : ℝ)) := by
  let A := 1 - q
  have hApos : 0 < A := by dsimp [A]; linarith [hq.2]
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hinv :
      Tendsto (fun U : ℝ => U⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinvSq :
      Tendsto (fun U : ℝ => U⁻¹ ^ 2) atTop (nhds 0) := by
    simpa using hinv.pow 2
  have hratio :
      Tendsto (fun U : ℝ => radius U / U) atTop (nhds 1) :=
    radius_div_tendsto_atTop
  have hnum :
      Tendsto
        (fun U : ℝ =>
          Real.sqrt q * U⁻¹ ^ 2 - A * (radius U / U))
        atTop (nhds (-A)) := by
    convert
      (tendsto_const_nhds.mul hinvSq).sub
        (tendsto_const_nhds.mul hratio) using 1 <;> ring
  have hden :
      Tendsto
        (fun U : ℝ => q * U⁻¹ ^ 2 + A)
        atTop (nhds A) := by
    convert
      (tendsto_const_nhds.mul hinvSq).add tendsto_const_nhds using 1 <;>
        ring
  have hquot :
      Tendsto
        (fun U : ℝ =>
          (Real.sqrt q * U⁻¹ ^ 2 - A * (radius U / U)) /
            (q * U⁻¹ ^ 2 + A))
        atTop (nhds (-1 : ℝ)) := by
    have hraw := hnum.div hden hAne
    have hraw' :
        Tendsto
          (fun U : ℝ =>
            (Real.sqrt q * U⁻¹ ^ 2 - A * (radius U / U)) /
              (q * U⁻¹ ^ 2 + A))
          atTop (nhds ((-A) / A)) := by
      apply hraw.congr'
      filter_upwards with U
      rfl
    have hlimit : (-A) / A = (-1 : ℝ) := by
      field_simp [hAne]
    simpa only [hlimit] using hraw'
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with U hU
  have hUne : U ≠ 0 := ne_of_gt (lt_trans zero_lt_one hU)
  dsimp [A]
  unfold targetCos
  field_simp [hUne]

lemma targetAngle_tendsto_atTop
    {q : ℝ} (hq : UnitRatio q) :
    Tendsto (targetAngleValue q) atTop (nhds Real.pi) := by
  have h :=
    Real.continuous_arccos.continuousAt.tendsto.comp
      (targetCos_tendsto_atTop hq)
  rw [Real.arccos_neg_one] at h
  unfold targetAngleValue
  apply h.congr'
  filter_upwards with U
  rfl

namespace Internal

/-- The complete target-angle package, including the corrected derivative. -/
theorem targetAngle (q : ℝ) (hq : UnitRatio q) :
    TargetAngleResult q where
  range := targetAngle_range hq
  continuousOn := targetAngle_continuousOn hq
  strictMonoOn := targetAngle_strictMonoOn hq
  targetCos_derivative := targetCos_hasDerivAt hq
  tendsto_one := targetAngle_tendsto_one hq
  tendsto_atTop := targetAngle_tendsto_atTop hq

end Internal

end ITEMf
