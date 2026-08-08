import ITEMf.Spec.Construction

/-!
# The ITEM-f one-step shooting map

This file proves the three assertions in
`lem:app-itemf-one-step`: the arccos domain, strict angle monotonicity, and
strict decrease with the shooting parameter when the cosine is negative.
-/

open Set

set_option autoImplicit false

namespace ITEMf

lemma oneStepArg_mem_Ioo
    {q p : ℝ} (hq : UnitRatio q) (hp0 : 0 < p) (hpq : p < q)
    (theta : ℝ) :
    oneStepArg q p theta ∈ Ioo (-1 : ℝ) 1 := by
  rcases hq with ⟨hq0, hq1⟩
  have hcosLower : -1 ≤ Real.cos theta := Real.neg_one_le_cos theta
  have hcosUpper : Real.cos theta ≤ 1 := Real.cos_le_one theta
  unfold oneStepArg
  constructor <;> nlinarith

lemma oneStep_increment_mem_Ioo
    {q p : ℝ} (hq : UnitRatio q) (hp0 : 0 < p) (hpq : p < q)
    (theta : ℝ) :
    oneStep q p theta - theta ∈ Ioo (0 : ℝ) Real.pi := by
  have harg := oneStepArg_mem_Ioo hq hp0 hpq theta
  unfold oneStep
  constructor
  · simpa only [add_sub_cancel_left] using
      (Real.arccos_pos.mpr harg.2)
  · simpa only [add_sub_cancel_left] using
      (Real.arccos_lt_pi.mpr harg.1)

lemma oneStepArg_hasDerivAt (q p theta : ℝ) :
    HasDerivAt (oneStepArg q p) (p * Real.sin theta) theta := by
  change
    HasDerivAt (fun x : ℝ => 1 - q - p * Real.cos x)
      (p * Real.sin theta) theta
  simpa only [mul_neg, neg_neg] using
    ((Real.hasDerivAt_cos theta).const_mul p).const_sub (1 - q)

lemma oneStep_square_bound
    {q p theta : ℝ} (hq : UnitRatio q) (hp0 : 0 < p) (hpq : p < q) :
    p ^ 2 * Real.sin theta ^ 2 +
        oneStepArg q p theta ^ 2 <
      1 := by
  rcases hq with ⟨hq0, hq1⟩
  have hcosLower : -1 ≤ Real.cos theta := Real.neg_one_le_cos theta
  have htrig := Real.sin_sq_add_cos_sq theta
  have hA : 0 < 1 - q := by linarith
  have hsum : 0 < p + (1 - q) := by positivity
  have hsumOne : p + (1 - q) < 1 := by linarith
  have honeCos : 0 ≤ 1 + Real.cos theta := by linarith
  have hnonneg :
      0 ≤ 2 * p * (1 - q) * (1 + Real.cos theta) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp0.le) hA.le) honeCos
  have hid :
      (p + (1 - q)) ^ 2 -
          (p ^ 2 * Real.sin theta ^ 2 +
            (1 - q - p * Real.cos theta) ^ 2) =
        2 * p * (1 - q) * (1 + Real.cos theta) := by
    nlinarith
  have hbound :
      p ^ 2 * Real.sin theta ^ 2 +
          oneStepArg q p theta ^ 2 ≤
        (p + (1 - q)) ^ 2 := by
    unfold oneStepArg
    linarith
  have hsquare : (p + (1 - q)) ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hsumOne) (add_pos hsum zero_lt_one)]
  exact hbound.trans_lt hsquare

lemma oneStep_hasDerivAt
    {q p : ℝ} (hq : UnitRatio q) (hp0 : 0 < p) (hpq : p < q)
    (theta : ℝ) :
    HasDerivAt (oneStep q p)
      (1 - p * Real.sin theta /
        Real.sqrt (1 - oneStepArg q p theta ^ 2)) theta := by
  have harg := oneStepArg_mem_Ioo hq hp0 hpq theta
  have harccos :=
    (Real.hasDerivAt_arccos (ne_of_gt harg.1) (ne_of_lt harg.2)).comp
      theta (oneStepArg_hasDerivAt q p theta)
  let D : ℝ :=
    1 + (-(1 / Real.sqrt (1 - oneStepArg q p theta ^ 2)) *
      (p * Real.sin theta))
  have hsum :
      HasDerivAt
        (id + Real.arccos ∘ oneStepArg q p) D theta := by
    exact (hasDerivAt_id' theta).add harccos
  have heq :
      (fun x : ℝ => x + Real.arccos (oneStepArg q p x)) =ᶠ[nhds theta]
        (id + Real.arccos ∘ oneStepArg q p) := by
    filter_upwards with x
    rfl
  have hsum' :
      HasDerivAt
        (fun x : ℝ => x + Real.arccos (oneStepArg q p x)) D theta :=
    hsum.congr_of_eventuallyEq heq
  change
    HasDerivAt
      (fun x : ℝ => x + Real.arccos (oneStepArg q p x))
      (1 - p * Real.sin theta /
        Real.sqrt (1 - oneStepArg q p theta ^ 2)) theta
  convert hsum' using 1
  dsimp [D]
  ring

lemma oneStep_derivative_pos
    {q p : ℝ} (hq : UnitRatio q) (hp0 : 0 < p) (hpq : p < q)
    (theta : ℝ) :
    0 <
      1 - p * Real.sin theta /
        Real.sqrt (1 - oneStepArg q p theta ^ 2) := by
  have hsquare := oneStep_square_bound hq hp0 hpq (theta := theta)
  have hrad :
      0 < 1 - oneStepArg q p theta ^ 2 := by
    nlinarith [sq_nonneg (p * Real.sin theta)]
  have hsqrtpos :
      0 < Real.sqrt (1 - oneStepArg q p theta ^ 2) :=
    Real.sqrt_pos.2 hrad
  have hsqrtsq :
      Real.sqrt (1 - oneStepArg q p theta ^ 2) ^ 2 =
        1 - oneStepArg q p theta ^ 2 :=
    Real.sq_sqrt hrad.le
  have hnumerator :
      p * Real.sin theta <
        Real.sqrt (1 - oneStepArg q p theta ^ 2) := by
    by_cases hsin : 0 ≤ Real.sin theta
    · have hpSin : 0 ≤ p * Real.sin theta :=
        mul_nonneg hp0.le hsin
      nlinarith
    · have hpSin : p * Real.sin theta < 0 :=
        mul_neg_of_pos_of_neg hp0 (lt_of_not_ge hsin)
      linarith
  rw [sub_pos]
  exact (div_lt_one hsqrtpos).2 hnumerator

lemma oneStep_strictMono
    {q p : ℝ} (hq : UnitRatio q) (hp0 : 0 < p) (hpq : p < q) :
    StrictMono (oneStep q p) := by
  apply strictMono_of_deriv_pos
  intro theta
  rw [(oneStep_hasDerivAt hq hp0 hpq theta).deriv]
  exact oneStep_derivative_pos hq hp0 hpq theta

lemma oneStep_parameter_decreases
    {q p p' theta : ℝ}
    (hq : UnitRatio q) (hp0 : 0 < p) (hpq : p < q)
    (hp'0 : 0 < p') (hp'q : p' < q) (hpp' : p < p')
    (hcos : Real.cos theta < 0) :
    oneStep q p' theta < oneStep q p theta := by
  have hpMem := oneStepArg_mem_Ioo hq hp0 hpq theta
  have hp'Mem := oneStepArg_mem_Ioo hq hp'0 hp'q theta
  have harg :
      oneStepArg q p theta < oneStepArg q p' theta := by
    unfold oneStepArg
    nlinarith
  have harccos :
      Real.arccos (oneStepArg q p' theta) <
        Real.arccos (oneStepArg q p theta) :=
    Real.arccos_lt_arccos hpMem.1.le harg hp'Mem.2.le
  unfold oneStep
  linarith

namespace Internal

/-- The complete one-step map result used by the construction orbit. -/
theorem oneStepMap
    (q p : ℝ) (hq : UnitRatio q) (hp0 : 0 < p) (hpq : p < q) :
    OneStepMapResult q p where
  argument_mem := oneStepArg_mem_Ioo hq hp0 hpq
  step_mem := oneStep_increment_mem_Ioo hq hp0 hpq
  angle_strictMono := oneStep_strictMono hq hp0 hpq
  parameter_decreases := by
    intro p' theta hp'0 hp'q hpp' hcos
    exact oneStep_parameter_decreases hq hp0 hpq hp'0 hp'q hpp' hcos

end Internal
end ITEMf
