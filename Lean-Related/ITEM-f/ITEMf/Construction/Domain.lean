import ITEMf.Construction.OneStep

/-!
# Candidate-domain facts

These lemmas isolate all square-root, inverse, and positivity obligations used
by the shooting construction.
-/

open Set Filter

set_option autoImplicit false

namespace ITEMf

lemma radiusSq_pos {Upsilon : ℝ} (hUpsilon : 1 < Upsilon) :
    0 < radiusSq Upsilon := by
  unfold radiusSq
  nlinarith [mul_pos (sub_pos.mpr hUpsilon) (add_pos_of_pos_of_nonneg
    (lt_trans zero_lt_one hUpsilon) zero_le_one)]

lemma radius_pos {Upsilon : ℝ} (hUpsilon : 1 < Upsilon) :
    0 < radius Upsilon := by
  exact Real.sqrt_pos.2 (radiusSq_pos hUpsilon)

lemma radius_sq {Upsilon : ℝ} (hUpsilon : 1 < Upsilon) :
    radius Upsilon ^ 2 = radiusSq Upsilon := by
  exact Real.sq_sqrt (radiusSq_pos hUpsilon).le

lemma radius_lt_upsilon {Upsilon : ℝ} (hUpsilon : 1 < Upsilon) :
    radius Upsilon < Upsilon := by
  have hUpos : 0 < Upsilon := lt_trans zero_lt_one hUpsilon
  unfold radius
  rw [Real.sqrt_lt' hUpos]
  nlinarith

lemma radius_hasDerivAt {Upsilon : ℝ} (hUpsilon : 1 < Upsilon) :
    HasDerivAt radius (Upsilon / radius Upsilon) Upsilon := by
  have hinner :
      HasDerivAt (fun u : ℝ => u ^ 2 - 1) (2 * Upsilon) Upsilon := by
    simpa using! ((hasDerivAt_id' Upsilon).pow 2).sub_const 1
  have hnonzero : Upsilon ^ 2 - 1 ≠ 0 :=
    ne_of_gt (radiusSq_pos hUpsilon)
  have hsqrt :=
    (Real.hasDerivAt_sqrt hnonzero).comp Upsilon hinner
  have hsqrt' :
      HasDerivAt (fun u : ℝ => Real.sqrt (u ^ 2 - 1))
        ((1 / (2 * Real.sqrt (Upsilon ^ 2 - 1))) *
          (2 * Upsilon)) Upsilon := by
    simpa [Function.comp_def] using! hsqrt
  change
    HasDerivAt (fun u : ℝ => Real.sqrt (u ^ 2 - 1))
      (Upsilon / radius Upsilon) Upsilon
  convert hsqrt' using 1
  have hRne : radius Upsilon ≠ 0 := ne_of_gt (radius_pos hUpsilon)
  change
    Upsilon / radius Upsilon =
      (1 / (2 * radius Upsilon)) * (2 * Upsilon)
  field_simp

lemma candidateRadicand_pos {Upsilon : ℝ} (hUpsilon : 1 < Upsilon) :
    0 < 1 - Upsilon⁻¹ ^ 2 := by
  have hUpos : 0 < Upsilon := lt_trans zero_lt_one hUpsilon
  have hinvpos : 0 < Upsilon⁻¹ := inv_pos.mpr hUpos
  have hinvlt : Upsilon⁻¹ < 1 := (inv_lt_one₀ hUpos).2 hUpsilon
  nlinarith [mul_pos (sub_pos.mpr hinvlt) (add_pos hinvpos zero_lt_one)]

lemma candidateP_pos
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    0 < candidateP q Upsilon := by
  unfold candidateP
  exact mul_pos hq.1 (Real.sqrt_pos.2 (candidateRadicand_pos hUpsilon))

lemma candidateP_lt_q
    {q Upsilon : ℝ} (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    candidateP q Upsilon < q := by
  have hrad : 0 < 1 - Upsilon⁻¹ ^ 2 :=
    candidateRadicand_pos hUpsilon
  have hinvSq : 0 < Upsilon⁻¹ ^ 2 := sq_pos_of_pos
    (inv_pos.mpr (lt_trans zero_lt_one hUpsilon))
  have hsqrt : Real.sqrt (1 - Upsilon⁻¹ ^ 2) < 1 := by
    rw [Real.sqrt_lt' zero_lt_one]
    nlinarith
  unfold candidateP
  simpa only [mul_one] using mul_lt_mul_of_pos_left hsqrt hq.1

lemma candidateP_eq_q_mul_radius_div
    {q Upsilon : ℝ} (hUpsilon : 1 < Upsilon) :
    candidateP q Upsilon = q * radius Upsilon / Upsilon := by
  have hUpos : 0 < Upsilon := lt_trans zero_lt_one hUpsilon
  have hUne : Upsilon ≠ 0 := ne_of_gt hUpos
  have hrad0 : 0 ≤ 1 - Upsilon⁻¹ ^ 2 :=
    (candidateRadicand_pos hUpsilon).le
  have hradiusSq := radius_sq hUpsilon
  have hcandidateSq := Real.sq_sqrt hrad0
  have hleft0 : 0 ≤ Real.sqrt (1 - Upsilon⁻¹ ^ 2) :=
    Real.sqrt_nonneg _
  have hright0 : 0 ≤ radius Upsilon / Upsilon :=
    div_nonneg (Real.sqrt_nonneg _) hUpos.le
  have hsquares :
      Real.sqrt (1 - Upsilon⁻¹ ^ 2) ^ 2 =
        (radius Upsilon / Upsilon) ^ 2 := by
    rw [hcandidateSq]
    field_simp
    unfold radiusSq at hradiusSq
    nlinarith
  have heq :
      Real.sqrt (1 - Upsilon⁻¹ ^ 2) = radius Upsilon / Upsilon := by
    nlinarith
  unfold candidateP
  rw [heq]
  ring

lemma candidateP_strictMonoOn
    {q : ℝ} (hq : UnitRatio q) :
    StrictMonoOn (candidateP q) (Ioi (1 : ℝ)) := by
  intro U hU V hV hUV
  have hUpos : 0 < U := lt_trans zero_lt_one hU
  have hVpos : 0 < V := lt_trans zero_lt_one hV
  have hinv : V⁻¹ < U⁻¹ := (inv_lt_inv₀ hVpos hUpos).2 hUV
  have hinvU0 : 0 ≤ U⁻¹ := (inv_pos.mpr hUpos).le
  have hinvV0 : 0 ≤ V⁻¹ := (inv_pos.mpr hVpos).le
  have hinvSq : V⁻¹ ^ 2 < U⁻¹ ^ 2 :=
    (sq_lt_sq₀ hinvV0 hinvU0).2 hinv
  have hrad :
      1 - U⁻¹ ^ 2 < 1 - V⁻¹ ^ 2 := by linarith
  have hsqrt :=
    Real.strictMonoOn_sqrt
      (candidateRadicand_pos hU).le
      (candidateRadicand_pos hV).le hrad
  unfold candidateP
  exact mul_lt_mul_of_pos_left hsqrt hq.1

lemma candidateP_continuousOn (q : ℝ) :
    ContinuousOn (candidateP q) (Ioi (1 : ℝ)) := by
  unfold candidateP
  apply continuousOn_const.mul
  apply ContinuousOn.sqrt
  apply continuousOn_const.sub
  apply ContinuousOn.pow
  apply ContinuousOn.inv₀ continuousOn_id
  intro U hU
  exact ne_of_gt (lt_trans zero_lt_one hU)

lemma candidateP_tendsto_one (q : ℝ) :
    Tendsto (candidateP q) (nhdsWithin (1 : ℝ) (Ioi 1)) (nhds 0) := by
  have hcont :
      ContinuousAt
        (fun U : ℝ => q * Real.sqrt (1 - U⁻¹ ^ 2)) 1 := by
    have hinv : ContinuousAt (fun U : ℝ => U⁻¹) 1 :=
      continuousAt_id.inv₀ one_ne_zero
    exact continuousAt_const.mul (continuousAt_const.sub (hinv.pow 2)).sqrt
  have htendsto :=
    hcont.tendsto.mono_left
      (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left)
  change
    Tendsto (fun U : ℝ => q * Real.sqrt (1 - U⁻¹ ^ 2))
      (nhdsWithin (1 : ℝ) (Ioi 1)) (nhds 0)
  simpa only [inv_one, one_pow, sub_self, Real.sqrt_zero, mul_zero] using
    htendsto

lemma candidateP_tendsto_atTop (q : ℝ) :
    Tendsto (candidateP q) atTop (nhds q) := by
  have hinv :
      Tendsto (fun U : ℝ => U⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hrad :
      Tendsto (fun U : ℝ => 1 - U⁻¹ ^ 2) atTop (nhds 1) := by
    simpa using (hinv.pow 2).const_sub 1
  have hsqrt :
      Tendsto (fun U : ℝ => Real.sqrt (1 - U⁻¹ ^ 2))
        atTop (nhds 1) := by
    simpa using hrad.sqrt
  change
    Tendsto (fun U : ℝ => q * Real.sqrt (1 - U⁻¹ ^ 2))
      atTop (nhds q)
  simpa only [Real.sqrt_one, mul_one] using hsqrt.const_mul q

lemma radius_div_tendsto_atTop :
    Tendsto (fun U : ℝ => radius U / U) atTop (nhds 1) := by
  have hinv :
      Tendsto (fun U : ℝ => U⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hrad :
      Tendsto (fun U : ℝ => 1 - U⁻¹ ^ 2) atTop (nhds 1) := by
    simpa using (hinv.pow 2).const_sub 1
  have hsqrt :
      Tendsto (fun U : ℝ => Real.sqrt (1 - U⁻¹ ^ 2))
        atTop (nhds 1) := by
    simpa using hrad.sqrt
  apply hsqrt.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with U hU
  simpa [candidateP] using
    (candidateP_eq_q_mul_radius_div (q := 1) hU)

lemma radius_tendsto_one :
    Tendsto radius (nhdsWithin (1 : ℝ) (Ioi 1)) (nhds 0) := by
  have hcont :
      ContinuousAt (fun U : ℝ => Real.sqrt (U ^ 2 - 1)) 1 := by
    fun_prop
  have htendsto :=
    hcont.tendsto.mono_left
      (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left)
  unfold radius
  simpa using htendsto

end ITEMf
