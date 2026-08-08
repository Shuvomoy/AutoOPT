import Mathlib

/-!
# The scalar one-step map

This file formalizes the admissible root of

`Ω * (r - t) ^ 2 = r * (1 - t ^ 2)`.

The clipped definition is total and continuous on the shooting rectangle
`1 ≤ Ω`, `0 ≤ r ≤ 1`.  On the admissible region `1 ≤ Ω * r`, the clipping
is inactive and the map is the unique root in `[0,r)`.
-/

open Set

set_option autoImplicit false

namespace LemniAcc

/-- The polynomial one-step recurrence relation. -/
def OneStepRel (Ω r t : ℝ) : Prop :=
  Ω * (r - t) ^ 2 = r * (1 - t ^ 2)

/-- The domain on which the lower root is admissible. -/
def OneStepDomain (Ω r : ℝ) : Prop :=
  0 < Ω ∧ 0 < r ∧ r ≤ 1 ∧ 1 ≤ Ω * r

/-- The quarter-discriminant of the one-step quadratic. -/
def oneStepDiscriminant (Ω r : ℝ) : ℝ :=
  r ^ 2 + Ω * r * (1 - r ^ 2)

/-- The lower root of the one-step quadratic before clipping. -/
noncomputable def oneStepRaw (Ω r : ℝ) : ℝ :=
  (Ω * r - Real.sqrt (oneStepDiscriminant Ω r)) / (Ω + r)

/-- The total one-step shooting map.  The `max` makes failed shots stick at
zero while leaving every admissible step unchanged. -/
noncomputable def oneStep (Ω r : ℝ) : ℝ :=
  max 0 (oneStepRaw Ω r)

lemma oneStepDiscriminant_nonneg
    {Ω r : ℝ} (hΩ : 0 ≤ Ω) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ oneStepDiscriminant Ω r := by
  unfold oneStepDiscriminant
  have hsq : 0 ≤ 1 - r ^ 2 := by nlinarith [sq_nonneg (1 - r)]
  positivity

lemma oneStepDiscriminant_pos
    {Ω r : ℝ} (hr : 0 < r) (hΩ : 0 ≤ Ω) (hr1 : r ≤ 1) :
    0 < oneStepDiscriminant Ω r := by
  unfold oneStepDiscriminant
  have hsq : 0 ≤ 1 - r ^ 2 := by nlinarith [sq_nonneg (1 - r)]
  nlinarith [sq_pos_of_pos hr, mul_nonneg (mul_nonneg hΩ (le_of_lt hr)) hsq]

lemma oneStepDiscriminant_sqrt_sq
    {Ω r : ℝ} (hΩ : 0 ≤ Ω) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (Real.sqrt (oneStepDiscriminant Ω r)) ^ 2 =
      oneStepDiscriminant Ω r := by
  exact Real.sq_sqrt (oneStepDiscriminant_nonneg hΩ hr0 hr1)

lemma oneStep_sqrt_ge_r
    {Ω r : ℝ} (hΩ : 0 ≤ Ω) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r ≤ Real.sqrt (oneStepDiscriminant Ω r) := by
  have hD : 0 ≤ oneStepDiscriminant Ω r :=
    oneStepDiscriminant_nonneg hΩ hr0 hr1
  have hsqrt := Real.sq_sqrt hD
  have hsqrt0 := Real.sqrt_nonneg (oneStepDiscriminant Ω r)
  have hsq : 0 ≤ 1 - r ^ 2 := by nlinarith [sq_nonneg (1 - r)]
  have hle : r ^ 2 ≤ oneStepDiscriminant Ω r := by
    unfold oneStepDiscriminant
    have hprod : 0 ≤ Ω * r * (1 - r ^ 2) :=
      mul_nonneg (mul_nonneg hΩ hr0) hsq
    linarith
  nlinarith

lemma oneStepRaw_nonneg
    {Ω r : ℝ} (hdom : OneStepDomain Ω r) :
    0 ≤ oneStepRaw Ω r := by
  rcases hdom with ⟨hΩ, hr, hr1, hΩr⟩
  have hD : 0 ≤ oneStepDiscriminant Ω r :=
    oneStepDiscriminant_nonneg hΩ.le hr.le hr1
  have hden : 0 < Ω + r := by positivity
  apply div_nonneg
  · have hsqrt := Real.sq_sqrt hD
    have hsqrt0 := Real.sqrt_nonneg (oneStepDiscriminant Ω r)
    have hfactor :
        0 ≤ r * (Ω + r) * (Ω * r - 1) := by positivity
    have hsq :
        oneStepDiscriminant Ω r ≤ (Ω * r) ^ 2 := by
      unfold oneStepDiscriminant
      nlinarith
    nlinarith
  · exact hden.le

lemma oneStep_eq_raw
    {Ω r : ℝ} (hdom : OneStepDomain Ω r) :
    oneStep Ω r = oneStepRaw Ω r := by
  unfold oneStep
  exact max_eq_right (oneStepRaw_nonneg hdom)

lemma oneStepRaw_lt
    {Ω r : ℝ} (hΩ : 0 < Ω) (hr : 0 < r) :
    oneStepRaw Ω r < r := by
  unfold oneStepRaw
  have hden : 0 < Ω + r := by positivity
  rw [div_lt_iff₀ hden]
  have hsqrt : 0 ≤ Real.sqrt (oneStepDiscriminant Ω r) :=
    Real.sqrt_nonneg _
  nlinarith [sq_pos_of_pos hr]

lemma oneStep_lt
    {Ω r : ℝ} (hdom : OneStepDomain Ω r) :
    oneStep Ω r < r := by
  rw [oneStep_eq_raw hdom]
  exact oneStepRaw_lt hdom.1 hdom.2.1

lemma oneStep_nonneg (Ω r : ℝ) : 0 ≤ oneStep Ω r := by
  exact le_max_left _ _

lemma oneStepRaw_rel
    {Ω r : ℝ} (hΩ : 0 < Ω) (hr : 0 < r) (hr1 : r ≤ 1) :
    OneStepRel Ω r (oneStepRaw Ω r) := by
  unfold OneStepRel oneStepRaw
  have hden : Ω + r ≠ 0 := ne_of_gt (by positivity)
  have hD : 0 ≤ oneStepDiscriminant Ω r :=
    oneStepDiscriminant_nonneg hΩ.le hr.le hr1
  field_simp
  have hsqrt := Real.sq_sqrt hD
  unfold oneStepDiscriminant at hsqrt ⊢
  nlinarith

lemma oneStep_rel
    {Ω r : ℝ} (hdom : OneStepDomain Ω r) :
    OneStepRel Ω r (oneStep Ω r) := by
  rw [oneStep_eq_raw hdom]
  exact oneStepRaw_rel hdom.1 hdom.2.1 hdom.2.2.1

lemma oneStep_eq_zero_iff
    {Ω r : ℝ} (hdom : OneStepDomain Ω r) :
    oneStep Ω r = 0 ↔ Ω * r = 1 := by
  rw [oneStep_eq_raw hdom]
  constructor
  · intro h
    have hrel := oneStepRaw_rel hdom.1 hdom.2.1 hdom.2.2.1
    unfold OneStepRel at hrel
    rw [h] at hrel
    have hr := hdom.2.1
    nlinarith
  · intro h
    unfold oneStepRaw
    have hden : Ω + r ≠ 0 := ne_of_gt (add_pos hdom.1 hdom.2.1)
    apply (div_eq_zero_iff).2
    left
    have hD : oneStepDiscriminant Ω r = 1 := by
      unfold oneStepDiscriminant
      nlinarith
    rw [hD, Real.sqrt_one, h]
    norm_num

lemma oneStep_pos_iff
    {Ω r : ℝ} (hdom : OneStepDomain Ω r) :
    0 < oneStep Ω r ↔ 1 < Ω * r := by
  constructor
  · intro h
    rcases lt_or_eq_of_le hdom.2.2.2 with hlt | heq
    · exact hlt
    · have hz : oneStep Ω r = 0 := (oneStep_eq_zero_iff hdom).2 heq.symm
      nlinarith
  · intro h
    rcases lt_or_eq_of_le (oneStep_nonneg Ω r) with hpos | heq
    · exact hpos
    · have hz : oneStep Ω r = 0 := heq.symm
      have := (oneStep_eq_zero_iff hdom).1 hz
      linarith

/-- The upper quadratic root. -/
noncomputable def oneStepUpper (Ω r : ℝ) : ℝ :=
  (Ω * r + Real.sqrt (oneStepDiscriminant Ω r)) / (Ω + r)

lemma oneStepUpper_ge
    {Ω r : ℝ} (hdom : OneStepDomain Ω r) :
    r ≤ oneStepUpper Ω r := by
  rcases hdom with ⟨hΩ, hr, hr1, hΩr⟩
  unfold oneStepUpper
  have hden : 0 < Ω + r := by positivity
  rw [le_div_iff₀ hden]
  have hsqrt : r ≤ Real.sqrt (oneStepDiscriminant Ω r) :=
    oneStep_sqrt_ge_r hΩ.le hr.le hr1
  nlinarith [sq_nonneg r]

lemma oneStep_unique
    {Ω r t : ℝ} (hdom : OneStepDomain Ω r)
    (_ht0 : 0 ≤ t) (htr : t < r) (hrel : OneStepRel Ω r t) :
    t = oneStep Ω r := by
  rw [oneStep_eq_raw hdom]
  let f := oneStepRaw Ω r
  have hfrel : OneStepRel Ω r f :=
    oneStepRaw_rel hdom.1 hdom.2.1 hdom.2.2.1
  have hf : f < r := oneStepRaw_lt hdom.1 hdom.2.1
  have hquad_t :
      (Ω + r) * t ^ 2 - 2 * Ω * r * t + Ω * r ^ 2 - r = 0 := by
    unfold OneStepRel at hrel
    nlinarith
  have hquad_f :
      (Ω + r) * f ^ 2 - 2 * Ω * r * f + Ω * r ^ 2 - r = 0 := by
    unfold OneStepRel at hfrel
    nlinarith
  by_contra hne
  have hsum : (Ω + r) * (t + f) = 2 * Ω * r := by
    have hfactor :
        (t - f) * ((Ω + r) * (t + f) - 2 * Ω * r) = 0 := by
      nlinarith
    have hz := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
    nlinarith
  have ht_upper : t = oneStepUpper Ω r := by
    unfold f oneStepRaw at hsum
    unfold oneStepUpper
    have hden : Ω + r ≠ 0 := ne_of_gt (add_pos hdom.1 hdom.2.1)
    field_simp at hsum ⊢
    nlinarith
  rw [ht_upper] at htr
  exact (not_lt_of_ge (oneStepUpper_ge hdom)) htr

lemma oneStep_characterization
    {Ω r t : ℝ} (hdom : OneStepDomain Ω r) :
    OneStepRel Ω r t ∧ 0 ≤ t ∧ t < r ↔ t = oneStep Ω r := by
  constructor
  · rintro ⟨hrel, ht0, htr⟩
    exact oneStep_unique hdom ht0 htr hrel
  · rintro rfl
    exact ⟨oneStep_rel hdom, oneStep_nonneg _ _, oneStep_lt hdom⟩

lemma oneStep_decrement_nonneg
    {Ω r : ℝ} (hdom : OneStepDomain Ω r) :
    0 ≤ r - oneStep Ω r :=
  sub_nonneg.mpr (oneStep_lt hdom).le

lemma oneStep_decrement_le_invSqrt
    {Ω r : ℝ} (hdom : OneStepDomain Ω r) :
    r - oneStep Ω r ≤ 1 / Real.sqrt Ω := by
  let t := oneStep Ω r
  have ht0 : 0 ≤ t := oneStep_nonneg _ _
  have htr : t < r := oneStep_lt hdom
  have ht1 : t ≤ 1 := htr.le.trans hdom.2.2.1
  have hfac0 : 0 ≤ 1 - t ^ 2 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hrhs : r * (1 - t ^ 2) ≤ 1 := by
    have hnonneg : 0 ≤ (1 - r) + r * t ^ 2 :=
      add_nonneg (sub_nonneg.mpr hdom.2.2.1)
        (mul_nonneg hdom.2.1.le (sq_nonneg t))
    nlinarith
  have hrel : Ω * (r - t) ^ 2 = r * (1 - t ^ 2) :=
    oneStep_rel hdom
  have hsqrt0 : 0 ≤ Real.sqrt Ω := Real.sqrt_nonneg _
  have hsqrtpos : 0 < Real.sqrt Ω := Real.sqrt_pos.2 hdom.1
  have hsqrtsq : (Real.sqrt Ω) ^ 2 = Ω := Real.sq_sqrt hdom.1.le
  have hdelta0 : 0 ≤ r - t := sub_nonneg.mpr htr.le
  have hproduct0 : 0 ≤ Real.sqrt Ω * (r - t) := mul_nonneg hsqrt0 hdelta0
  have hproductsq : (Real.sqrt Ω * (r - t)) ^ 2 ≤ 1 := by
    rw [mul_pow, hsqrtsq]
    nlinarith
  have hproduct : Real.sqrt Ω * (r - t) ≤ 1 := by
    nlinarith [sq_nonneg (Real.sqrt Ω * (r - t) - 1)]
  change r - t ≤ 1 / Real.sqrt Ω
  rw [le_div_iff₀ hsqrtpos]
  nlinarith

/-- The parameter recovered from a nonterminal pair `(r,t)`. -/
noncomputable def stepParameter (r t : ℝ) : ℝ :=
  r * (1 - t ^ 2) / (r - t) ^ 2

lemma stepParameter_eq
    {Ω r t : ℝ} (hrt : t < r) (hrel : OneStepRel Ω r t) :
    stepParameter r t = Ω := by
  unfold stepParameter
  rw [div_eq_iff (pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hrt)))]
  exact hrel.symm

lemma stepParameter_strictMono
    {r a b : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (ha : 0 ≤ a) (hab : a < b) (hbr : b < r) :
    stepParameter r a < stepParameter r b := by
  have har : 0 < r - a := by linarith
  have hbr' : 0 < r - b := by linarith
  have hb0 : 0 ≤ b := ha.trans hab.le
  have hba1 : b < 1 := hbr.trans_le hr1
  have haa1 : a < 1 := hab.trans hba1
  have h1rb : 0 < 1 - r * b := by
    have hpos : 0 < r * (1 - b) := mul_pos hr (by linarith)
    have hnonneg : 0 ≤ (1 - r) := by linarith
    nlinarith
  have h1ra : 0 < 1 - r * a := by
    have hpos : 0 < r * (1 - a) := mul_pos hr (by linarith)
    have hnonneg : 0 ≤ (1 - r) := by linarith
    nlinarith
  have hkernel :
      0 < (r - a) * (1 - r * b) + (r - b) * (1 - r * a) := by
    positivity
  have hid :
      r * (1 - b ^ 2) * (r - a) ^ 2 -
          r * (1 - a ^ 2) * (r - b) ^ 2 =
        r * (b - a) *
          ((r - a) * (1 - r * b) + (r - b) * (1 - r * a)) := by
    ring
  unfold stepParameter
  rw [div_lt_div_iff₀ (sq_pos_of_pos har) (sq_pos_of_pos hbr')]
  rw [← sub_pos]
  rw [hid]
  positivity

lemma oneStep_strictMono_omega
    {Ω Ω' r : ℝ} (hΩ : Ω < Ω')
    (hdom : OneStepDomain Ω r) (hdom' : OneStepDomain Ω' r) :
    oneStep Ω r < oneStep Ω' r := by
  let a := oneStep Ω r
  let b := oneStep Ω' r
  have ha0 : 0 ≤ a := oneStep_nonneg _ _
  have hb0 : 0 ≤ b := oneStep_nonneg _ _
  have har : a < r := oneStep_lt hdom
  have hbr : b < r := oneStep_lt hdom'
  have hpa : stepParameter r a = Ω :=
    stepParameter_eq har (oneStep_rel hdom)
  have hpb : stepParameter r b = Ω' :=
    stepParameter_eq hbr (oneStep_rel hdom')
  by_contra hnot
  have hba : b ≤ a := le_of_not_gt hnot
  rcases hba.lt_or_eq with hlt | heq
  · have hpba : stepParameter r b < stepParameter r a :=
      stepParameter_strictMono hdom.2.1 hdom.2.2.1 hb0 hlt har
    linarith
  · rw [heq] at hpb
    linarith

lemma oneStep_strictMono_rho
    {Ω r s : ℝ} (hrs : r < s)
    (hdom : OneStepDomain Ω r) (hdoms : OneStepDomain Ω s) :
    oneStep Ω r < oneStep Ω s := by
  let a := oneStep Ω r
  let b := oneStep Ω s
  have ha0 : 0 ≤ a := oneStep_nonneg _ _
  have hb0 : 0 ≤ b := oneStep_nonneg _ _
  have har : a < r := oneStep_lt hdom
  have hbs : b < s := oneStep_lt hdoms
  have harels : OneStepRel Ω r a := oneStep_rel hdom
  have hpb : stepParameter s b = Ω :=
    stepParameter_eq hbs (oneStep_rel hdoms)
  have has : a < s := har.trans hrs
  have hrs0 : 0 < s - r := sub_pos.mpr hrs
  have hrsa : 0 < r * s - a ^ 2 := by
    have haa : a ^ 2 < r ^ 2 := by
      have hsum : 0 < r + a := by nlinarith [hdom.2.1]
      have hprod : 0 < (r - a) * (r + a) :=
        mul_pos (sub_pos.mpr har) hsum
      nlinarith
    have hrrs : r ^ 2 < r * s := by
      nlinarith [mul_pos hdom.2.1 hrs0]
    linarith
  have hscaled :
      r * (Ω * (s - a) ^ 2 - s * (1 - a ^ 2)) =
        Ω * (s - r) * (r * s - a ^ 2) := by
    unfold OneStepRel at harels
    nlinarith
  have hpsi : 0 < Ω * (s - a) ^ 2 - s * (1 - a ^ 2) := by
    have hright : 0 < Ω * (s - r) * (r * s - a ^ 2) :=
      mul_pos (mul_pos hdom.1 hrs0) hrsa
    nlinarith
  have hpa : stepParameter s a < Ω := by
    unfold stepParameter
    rw [div_lt_iff₀ (sq_pos_of_pos (sub_pos.mpr has))]
    nlinarith
  by_contra hnot
  have hba : b ≤ a := le_of_not_gt hnot
  rcases hba.lt_or_eq with hlt | heq
  · have hpba : stepParameter s b < stepParameter s a :=
      stepParameter_strictMono hdoms.2.1 hdoms.2.2.1 hb0 hlt has
    linarith
  · rw [heq] at hpb
    linarith

lemma oneStep_strictMono_both
    {Ω Ω' r s : ℝ} (hΩ : Ω < Ω') (hrs : r ≤ s)
    (hdom : OneStepDomain Ω r) (hdoms : OneStepDomain Ω' s) :
    oneStep Ω r < oneStep Ω' s := by
  have hdom' : OneStepDomain Ω' r := by
    refine ⟨hdoms.1, hdom.2.1, hdom.2.2.1, ?_⟩
    have hΩ0 : 0 < Ω := hdom.1
    have hr0 : 0 < r := hdom.2.1
    have hprod : Ω * r < Ω' * r := mul_lt_mul_of_pos_right hΩ hr0
    exact hdom.2.2.2.trans hprod.le
  have hfirst :
      oneStep Ω r < oneStep Ω' r :=
    oneStep_strictMono_omega hΩ hdom hdom'
  rcases hrs.lt_or_eq with hrs' | rfl
  · exact hfirst.trans (oneStep_strictMono_rho hrs' hdom' hdoms)
  · exact hfirst

lemma oneStep_le
    {Ω r : ℝ} (hΩ : 1 ≤ Ω) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    oneStep Ω r ≤ r := by
  by_cases hr : r = 0
  · subst r
    simp [oneStep, oneStepRaw, oneStepDiscriminant]
  by_cases hΩr : 1 ≤ Ω * r
  · exact (oneStep_lt ⟨lt_of_lt_of_le zero_lt_one hΩ, lt_of_le_of_ne hr0 (Ne.symm hr),
        hr1, hΩr⟩).le
  · have hraw : oneStepRaw Ω r ≤ 0 := by
      unfold oneStepRaw
      have hden : 0 < Ω + r := by positivity
      have hstrict : Ω * r < 1 := lt_of_not_ge hΩr
      have hD : 0 ≤ oneStepDiscriminant Ω r :=
        oneStepDiscriminant_nonneg (zero_le_one.trans hΩ) hr0 hr1
      have hsqrt := Real.sq_sqrt hD
      have hsqrt0 := Real.sqrt_nonneg (oneStepDiscriminant Ω r)
      have hfactor :
          r * (Ω + r) * (Ω * r - 1) ≤ 0 := by
        have hlast : Ω * r - 1 ≤ 0 := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg hr0 hden.le) hlast
      have hsq : (Ω * r) ^ 2 ≤ oneStepDiscriminant Ω r := by
        unfold oneStepDiscriminant
        nlinarith
      have hnum : Ω * r - Real.sqrt (oneStepDiscriminant Ω r) ≤ 0 := by
        nlinarith
      exact div_nonpos_of_nonpos_of_nonneg hnum hden.le
    unfold oneStep
    rw [max_eq_left hraw]
    exact hr0

lemma oneStep_mem_Icc
    {Ω r : ℝ} (hΩ : 1 ≤ Ω) (hr : r ∈ Icc (0 : ℝ) 1) :
    oneStep Ω r ∈ Icc (0 : ℝ) 1 := by
  exact ⟨oneStep_nonneg _ _, (oneStep_le hΩ hr.1 hr.2).trans hr.2⟩

lemma continuousOn_oneStep :
    ContinuousOn (fun p : ℝ × ℝ => oneStep p.1 p.2)
      (Ici (1 : ℝ) ×ˢ Icc (0 : ℝ) 1) := by
  intro p hp
  unfold oneStep oneStepRaw oneStepDiscriminant
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_const.max
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact ne_of_gt (add_pos_of_pos_of_nonneg
      (lt_of_lt_of_le zero_lt_one hp.1) hp.2.1)

lemma oneStep_continuousAt
    {Ω r : ℝ} (hΩ : 1 < Ω) (hr0 : 0 < r) (_hr1 : r < 1) :
    ContinuousAt (fun p : ℝ × ℝ => oneStep p.1 p.2) (Ω, r) := by
  unfold oneStep oneStepRaw oneStepDiscriminant
  apply continuousAt_const.max
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · positivity

end LemniAcc
