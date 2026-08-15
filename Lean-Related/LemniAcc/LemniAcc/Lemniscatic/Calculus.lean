import LemniAcc.Lemniscatic.Integral

open scoped Interval Topology
open Set MeasureTheory intervalIntegral Filter

set_option autoImplicit false

namespace LemniAcc.Lemniscatic

theorem arcsl_continuousOn :
    ContinuousOn arcsl (Icc (0 : ℝ) 1) := by
  change ContinuousOn
    (fun b : ℝ => ∫ x in (0 : ℝ)..b, arcslIntegrand x) (Icc 0 1)
  simpa [uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval'
      arcslIntegrand_intervalIntegrable
      (left_mem_uIcc : (0 : ℝ) ∈ [[(0 : ℝ), 1]])

theorem arcsl_hasDerivAt {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt arcsl (arcslIntegrand u) u := by
  have hint : IntervalIntegrable arcslIntegrand volume (0 : ℝ) u :=
    arcslIntegrand_intervalIntegrable.mono
      (c := (0 : ℝ)) (d := u)
      (by
        rw [uIcc_of_le hu.1.le, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hu.2.le)
      le_rfl
  have hcont :=
    arcslIntegrand_continuousAt
      (x := u) ⟨by linarith [hu.1], hu.2⟩
  have hmeas : AEStronglyMeasurable arcslIntegrand volume := by
    unfold arcslIntegrand
    fun_prop
  simpa only [arcsl] using!
    intervalIntegral.integral_hasDerivAt_right hint
      hmeas.stronglyMeasurableAtFilter hcont

theorem arcsl_hasDerivAt_zero :
    HasDerivAt arcsl 1 0 := by
  have hcont :=
    arcslIntegrand_continuousAt
      (x := (0 : ℝ)) (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1)
  have hmeas : AEStronglyMeasurable arcslIntegrand volume := by
    unfold arcslIntegrand
    fun_prop
  have hint :
      IntervalIntegrable arcslIntegrand volume (0 : ℝ) 0 := by simp
  simpa [arcsl, arcslIntegrand] using!
    intervalIntegral.integral_hasDerivAt_right hint
      hmeas.stronglyMeasurableAtFilter hcont

theorem arcsl_strictMonoOn :
    StrictMonoOn arcsl (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have h0x : IntervalIntegrable arcslIntegrand volume (0 : ℝ) x :=
    arcslIntegrand_intervalIntegrable.mono
      (c := (0 : ℝ)) (d := x)
      (by
        rw [uIcc_of_le hx.1, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hx.2)
      le_rfl
  have hxyi : IntervalIntegrable arcslIntegrand volume x y :=
    arcslIntegrand_intervalIntegrable.mono
      (c := x) (d := y)
      (by
        rw [uIcc_of_le hxy.le, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc hx.1 hy.2)
      le_rfl
  have hpos : 0 < ∫ t in x..y, arcslIntegrand t :=
    intervalIntegral_pos_of_pos_on hxyi
      (fun t ht => arcslIntegrand_pos
        ⟨by linarith [hx.1, ht.1], by linarith [hy.2, ht.2]⟩)
      hxy
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals h0x hxyi
  simp only [arcsl] at hadd ⊢
  linarith

theorem arcsl_mapsTo :
    MapsTo arcsl (Icc (0 : ℝ) 1) (Icc (0 : ℝ) (varpi / 2)) := by
  intro u hu
  constructor
  · simpa using
      arcsl_strictMonoOn.monotoneOn
        (left_mem_Icc.2 zero_le_one) hu hu.1
  · simpa [arcsl_one] using
      arcsl_strictMonoOn.monotoneOn
        hu (right_mem_Icc.2 zero_le_one) hu.2

theorem arcsl_surjOn :
    SurjOn arcsl (Icc (0 : ℝ) 1) (Icc (0 : ℝ) (varpi / 2)) := by
  intro y hy
  have hy' : y ∈ Icc (arcsl 0) (arcsl 1) := by
    simpa [arcsl_zero, arcsl_one] using hy
  rcases intermediate_value_Icc zero_le_one arcsl_continuousOn hy' with
    ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

private noncomputable def arcslMap :
    Icc (0 : ℝ) 1 → Icc (0 : ℝ) (varpi / 2) :=
  fun u => ⟨arcsl u, arcsl_mapsTo u.2⟩

private theorem arcslMap_bijective :
    Function.Bijective arcslMap := by
  constructor
  · intro u v huv
    apply Subtype.ext
    apply arcsl_strictMonoOn.injOn u.2 v.2
    exact congrArg Subtype.val huv
  · intro y
    rcases arcsl_surjOn y.2 with ⟨u, hu, huy⟩
    exact ⟨⟨u, hu⟩, Subtype.ext huy⟩

private noncomputable def arcslEquiv :
    Icc (0 : ℝ) 1 ≃ Icc (0 : ℝ) (varpi / 2) :=
  Equiv.ofBijective arcslMap arcslMap_bijective

private theorem arcslEquiv_strictMono :
    StrictMono arcslEquiv := by
  intro u v huv
  exact arcsl_strictMonoOn u.2 v.2 huv

/-- The integral coordinate as an order isomorphism between its two
closed paper domains. -/
noncomputable def arcslOrderIso :
    Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) (varpi / 2) :=
  arcslEquiv.toOrderIso arcslEquiv_strictMono.monotone (by
    intro u v huv
    apply le_of_not_gt
    intro hvu
    have hcontra : arcslEquiv (arcslEquiv.symm v) <
        arcslEquiv (arcslEquiv.symm u) :=
      arcslEquiv_strictMono hvu
    have hvu' : v < u := by simpa using hcontra
    exact (not_lt_of_ge huv) hvu')

private noncomputable def angleClamp
    (x : ℝ) : Icc (0 : ℝ) (varpi / 2) :=
  ⟨angleClampValue x,
    le_min (le_max_right _ _) (div_nonneg varpi_pos.le (by norm_num)),
    min_le_right _ _⟩

private theorem angleClamp_eq {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (varpi / 2)) :
    angleClamp x = ⟨x, hx⟩ := by
  apply Subtype.ext
  simp [angleClamp, angleClampValue, max_eq_left hx.1, min_eq_left hx.2]

private theorem sl_preimage_exists (x : ℝ) :
    ∃ u : ℝ,
      u ∈ Icc (0 : ℝ) 1 ∧ arcsl u = angleClampValue x := by
  let u : Icc (0 : ℝ) 1 := arcslOrderIso.symm (angleClamp x)
  refine ⟨u, u.2, ?_⟩
  have happly := arcslOrderIso.apply_symm_apply (angleClamp x)
  exact congrArg Subtype.val happly

private theorem sl_eq_orderIso (x : ℝ) :
    sl x = (arcslOrderIso.symm (angleClamp x) : Icc (0 : ℝ) 1) := by
  classical
  rw [sl, dif_pos (sl_preimage_exists x)]
  apply arcsl_strictMonoOn.injOn
  · exact (Classical.choose_spec (sl_preimage_exists x)).1
  · exact (arcslOrderIso.symm (angleClamp x)).2
  · have hchosen := (Classical.choose_spec (sl_preimage_exists x)).2
    have hinverse := congrArg Subtype.val
      (arcslOrderIso.apply_symm_apply (angleClamp x))
    exact hchosen.trans hinverse.symm

@[simp] theorem arcsl_sl {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (varpi / 2)) :
    arcsl (sl x) = x := by
  have hclamp := angleClamp_eq hx
  have happly :=
    arcslOrderIso.apply_symm_apply (⟨x, hx⟩ : Icc (0 : ℝ) (varpi / 2))
  rw [sl_eq_orderIso]
  change (arcslOrderIso (arcslOrderIso.symm (angleClamp x))).1 = x
  rw [hclamp]
  exact congrArg Subtype.val happly

@[simp] theorem sl_arcsl {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    sl (arcsl u) = u := by
  have hmem := arcsl_mapsTo hu
  have hclamp := angleClamp_eq hmem
  have hinv :=
    arcslOrderIso.symm_apply_apply (⟨u, hu⟩ : Icc (0 : ℝ) 1)
  rw [sl_eq_orderIso]
  change (arcslOrderIso.symm (angleClamp (arcsl u))).1 = u
  rw [hclamp]
  exact congrArg Subtype.val hinv

@[simp] theorem sl_zero : sl 0 = 0 := by
  simpa using sl_arcsl (u := (0 : ℝ)) (left_mem_Icc.2 zero_le_one)

@[simp] theorem sl_varpi_half : sl (varpi / 2) = 1 := by
  simpa [arcsl_one] using
    sl_arcsl (u := (1 : ℝ)) (right_mem_Icc.2 zero_le_one)

theorem sl_mem_Icc (x : ℝ) : sl x ∈ Icc (0 : ℝ) 1 :=
  sl_eq_orderIso x ▸ (arcslOrderIso.symm (angleClamp x)).2

private theorem angleClamp_continuous : Continuous angleClamp := by
  exact (by fun_prop : Continuous fun x : ℝ =>
    min (max x 0) (varpi / 2)).subtype_mk _

theorem sl_continuous : Continuous sl := by
  rw [show sl = fun x : ℝ =>
      (arcslOrderIso.symm (angleClamp x)).1 from
    funext sl_eq_orderIso]
  exact continuous_subtype_val.comp
    (arcslOrderIso.toHomeomorph.continuous_invFun.comp angleClamp_continuous)

theorem sl_strictMonoOn :
    StrictMonoOn sl (Icc (0 : ℝ) (varpi / 2)) := by
  intro x hx y hy hxy
  have hcx := angleClamp_eq hx
  have hcy := angleClamp_eq hy
  rw [sl_eq_orderIso, sl_eq_orderIso]
  rw [hcx, hcy]
  exact arcslOrderIso.symm.strictMono hxy

theorem sl_mapsTo :
    MapsTo sl (Icc (0 : ℝ) (varpi / 2)) (Icc (0 : ℝ) 1) :=
  fun _ _ => sl_mem_Icc _

theorem sl_surjOn :
    SurjOn sl (Icc (0 : ℝ) (varpi / 2)) (Icc (0 : ℝ) 1) := by
  intro u hu
  exact ⟨arcsl u, arcsl_mapsTo hu, sl_arcsl hu⟩

theorem sl_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (varpi / 2)) :
    sl x ∈ Ioo (0 : ℝ) 1 := by
  have hx_closed : x ∈ Icc (0 : ℝ) (varpi / 2) := ⟨hx.1.le, hx.2.le⟩
  have hmem := sl_mem_Icc x
  constructor
  · apply lt_of_le_of_ne hmem.1
    intro hzero
    have hzero' : sl x = 0 := hzero.symm
    have hinv := arcsl_sl hx_closed
    rw [hzero', arcsl_zero] at hinv
    exact (ne_of_gt hx.1) hinv.symm
  · apply lt_of_le_of_ne hmem.2
    intro hone
    have hone' : sl x = 1 := hone
    have hinv := arcsl_sl hx_closed
    rw [hone', arcsl_one] at hinv
    exact (ne_of_lt hx.2) hinv.symm

theorem sl_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (varpi / 2)) :
    HasDerivAt sl (Real.sqrt (1 - sl x ^ 4)) x := by
  have hsli := sl_mem_Ioo hx
  have harc := arcsl_hasDerivAt hsli
  have hderiv_ne : arcslIntegrand (sl x) ≠ 0 :=
    (arcslIntegrand_pos
      ⟨by linarith [hsli.1], hsli.2⟩).ne'
  have hleft : ∀ᶠ y : ℝ in 𝓝 x, arcsl (sl y) = y := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact arcsl_sl ⟨hy.1.le, hy.2.le⟩
  have hinv :=
    harc.of_local_left_inverse sl_continuous.continuousAt hderiv_ne hleft
  simpa only [arcslIntegrand, inv_inv] using! hinv

private theorem sl_tendsto_nhdsGT_zero :
    Tendsto sl (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : Tendsto sl (𝓝 (0 : ℝ)) (𝓝 (sl 0)) :=
      sl_continuous.continuousAt
    change Tendsto sl (𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi 0)) (𝓝 (0 : ℝ))
    simpa using hcont.mono_left inf_le_left
  · have hhalf : 0 < varpi / 2 := div_pos varpi_pos (by norm_num)
    have hevlt : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), y < varpi / 2 :=
      (show ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), y < varpi / 2 from
        Iio_mem_nhds hhalf).filter_mono inf_le_left
    filter_upwards [eventually_mem_nhdsWithin, hevlt] with y hypos hylt
    exact (sl_mem_Ioo ⟨hypos, hylt⟩).1

theorem sl_sub_id_isLittleO :
    (fun x : ℝ => sl x - x) =o[𝓝[>] (0 : ℝ)] fun x : ℝ => x := by
  have hhalf : 0 < varpi / 2 := div_pos varpi_pos (by norm_num)
  have hevIoo :
      ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) (varpi / 2) := by
    have hevlt : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), y < varpi / 2 :=
      (show ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), y < varpi / 2 from
        Iio_mem_nhds hhalf).filter_mono inf_le_left
    filter_upwards [eventually_mem_nhdsWithin, hevlt] with x hx0 hxT
    exact ⟨hx0, hxT⟩
  have harc :=
    arcsl_hasDerivAt_zero.tendsto_slope_zero_right
  have hcomp := harc.comp sl_tendsto_nhdsGT_zero
  have hquotInv :
      Tendsto (fun x : ℝ => x / sl x)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    apply hcomp.congr'
    filter_upwards [hevIoo] with x hx
    simp only [Function.comp_apply, zero_add]
    rw [arcsl_sl ⟨hx.1.le, hx.2.le⟩, arcsl_zero]
    simp [div_eq_mul_inv, mul_comm, smul_eq_mul]
  have hquotInv' :=
    hquotInv.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hquot :
      Tendsto (fun x : ℝ => sl x / x)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hquotInv'' :
        Tendsto (fun x : ℝ => (x / sl x)⁻¹)
          (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      simpa using hquotInv'
    apply hquotInv''.congr'
    filter_upwards [hevIoo] with x hx
    have hxne : x ≠ 0 := hx.1.ne'
    have hslne : sl x ≠ 0 := (sl_mem_Ioo hx).1.ne'
    field_simp
  have hslope :
      Tendsto (slope sl 0)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    apply hquot.congr'
    filter_upwards [hevIoo] with x hx
    simp [slope_def_field, sl_zero, div_eq_mul_inv, mul_comm]
  have hderiv :
      HasDerivWithinAt sl 1 (Ioi (0 : ℝ)) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
    exact hslope
  simpa [sl_zero, smul_eq_mul] using hderiv.isLittleO

theorem sl_div_tendsto_one :
    Tendsto (fun x : ℝ => sl x / x)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hsum :
      Tendsto (fun x : ℝ => (sl x - x) / x + 1)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 + 1 : ℝ)) :=
    sl_sub_id_isLittleO.tendsto_div_nhds_zero.add tendsto_const_nhds
  have heq :
      (fun x : ℝ => (sl x - x) / x + 1) =ᶠ[𝓝[>] (0 : ℝ)]
        fun x : ℝ => sl x / x := by
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    rw [sub_div, div_self hxne]
    ring
  simpa only [zero_add] using hsum.congr' heq

@[simp] theorem cl_zero : cl 0 = 1 := by
  simp [cl]

@[simp] theorem cl_varpi_half : cl (varpi / 2) = 0 := by
  simp [cl]

theorem cl_continuous : Continuous cl := by
  unfold cl
  exact sl_continuous.comp (by fun_prop)

theorem cl_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (varpi / 2)) :
    HasDerivAt cl (-Real.sqrt (1 - cl x ^ 4)) x := by
  have hreflect :
      varpi / 2 - x ∈ Ioo (0 : ℝ) (varpi / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hinner :
      HasDerivAt (fun y : ℝ => varpi / 2 - y) (-1) x := by
    simpa using! (hasDerivAt_const x (varpi / 2)).sub (hasDerivAt_id' x)
  simpa [cl, Function.comp_def] using!
    (sl_hasDerivAt hreflect).comp x hinner

theorem cl_strictAntiOn :
    StrictAntiOn cl (Icc (0 : ℝ) (varpi / 2)) := by
  intro x hx y hy hxy
  have hx' :
      varpi / 2 - x ∈ Icc (0 : ℝ) (varpi / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' :
      varpi / 2 - y ∈ Icc (0 : ℝ) (varpi / 2) := by
    constructor <;> linarith [hy.1, hy.2]
  exact sl_strictMonoOn hy' hx' (by linarith)

theorem cl_mem_Icc (x : ℝ) : cl x ∈ Icc (0 : ℝ) 1 :=
  sl_mem_Icc _

theorem cl_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (varpi / 2)) :
    cl x ∈ Ioo (0 : ℝ) 1 := by
  unfold cl
  apply sl_mem_Ioo
  constructor <;> linarith [hx.1, hx.2]

theorem cl_surjOn :
    SurjOn cl (Icc (0 : ℝ) (varpi / 2)) (Icc (0 : ℝ) 1) := by
  intro u hu
  rcases sl_surjOn hu with ⟨x, hx, hxu⟩
  refine ⟨varpi / 2 - x, ?_, ?_⟩
  · constructor <;> linarith [hx.1, hx.2]
  · simpa [cl] using hxu

@[simp] theorem cl_complement (x : ℝ) :
    cl (varpi / 2 - x) = sl x := by
  simp [cl]

private noncomputable def complementRatio (u : ℝ) : ℝ :=
  (1 - u ^ 2) / (1 + u ^ 2)

private noncomputable def complementRoot (u : ℝ) : ℝ :=
  Real.sqrt (complementRatio u)

private theorem complementRatio_nonneg {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ complementRatio u := by
  unfold complementRatio
  have hu_sq : u ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  exact div_nonneg (by linarith) (by positivity)

private theorem complementRatio_le_one {u : ℝ}
    (_hu : u ∈ Icc (0 : ℝ) 1) :
    complementRatio u ≤ 1 := by
  unfold complementRatio
  apply (div_le_one (by positivity : (0 : ℝ) < 1 + u ^ 2)).2
  nlinarith [sq_nonneg u]

private theorem complementRoot_continuous : Continuous complementRoot := by
  unfold complementRoot complementRatio
  apply Real.continuous_sqrt.comp
  exact
    (continuous_const.sub (continuous_id.pow 2)).div₀
      (continuous_const.add (continuous_id.pow 2))
      (fun u => by nlinarith [sq_nonneg u])

private theorem complementRoot_mem_Icc {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    complementRoot u ∈ Icc (0 : ℝ) 1 := by
  exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.2 (complementRatio_le_one hu)⟩

private theorem complementRoot_mem_Ioo {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    complementRoot u ∈ Ioo (0 : ℝ) 1 := by
  have hu_closed : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  have hratio_pos : 0 < complementRatio u := by
    unfold complementRatio
    exact div_pos (by
      have : u ^ 2 < 1 := (sq_lt_one_iff₀ hu.1.le).2 hu.2
      linarith) (by positivity)
  have hratio_lt : complementRatio u < 1 := by
    unfold complementRatio
    rw [div_lt_one (by positivity : (0 : ℝ) < 1 + u ^ 2)]
    nlinarith [sq_pos_of_pos hu.1]
  constructor
  · exact Real.sqrt_pos.2 hratio_pos
  · apply lt_of_le_of_ne (Real.sqrt_le_one.2 hratio_lt.le)
    intro hone
    have hsquare := congrArg (fun z : ℝ => z ^ 2) hone
    rw [Real.sq_sqrt (complementRatio_nonneg hu_closed)] at hsquare
    norm_num at hsquare
    linarith

private theorem complementRatio_hasDerivAt (u : ℝ) :
    HasDerivAt complementRatio
      (-4 * u / (1 + u ^ 2) ^ 2) u := by
  have hnum :
      HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * u) u := by
    simpa using! ((hasDerivAt_id' u).pow 2).const_sub 1
  have hden :
      HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * u) u := by
    simpa using! ((hasDerivAt_id' u).pow 2).const_add 1
  have hraw :
      HasDerivAt complementRatio
        (((-2 * u) * (1 + u ^ 2) -
          (1 - u ^ 2) * (2 * u)) / (1 + u ^ 2) ^ 2) u := by
    simpa only [complementRatio] using!
      hnum.div hden (by positivity : (1 + u ^ 2) ≠ 0)
  convert hraw using 1
  ring

private theorem complementRoot_hasDerivAt {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt complementRoot
      (-2 * u / (complementRoot u * (1 + u ^ 2) ^ 2)) u := by
  have hu_closed : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  have hratio_pos : 0 < complementRatio u := by
    unfold complementRatio
    exact div_pos (by
      have : u ^ 2 < 1 := (sq_lt_one_iff₀ hu.1.le).2 hu.2
      linarith) (by positivity)
  have hraw :
      HasDerivAt complementRoot
        ((-4 * u / (1 + u ^ 2) ^ 2) /
          (2 * complementRoot u)) u := by
    simpa only [complementRoot] using!
      (complementRatio_hasDerivAt u).sqrt hratio_pos.ne'
  convert hraw using 1
  have hroot_ne : complementRoot u ≠ 0 :=
    (complementRoot_mem_Ioo hu).1.ne'
  have hden_ne : 1 + u ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private theorem complementRoot_mul_one_add_sq {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    complementRoot u * (1 + u ^ 2) =
      Real.sqrt (1 - u ^ 4) := by
  have hv := complementRoot_mem_Icc hu
  have hu_sq : u ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  have hu_four : u ^ 4 ≤ 1 := by
    calc
      u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ ≤ 1 := (sq_le_one_iff₀ (sq_nonneg u)).2 hu_sq
  have hv_sq :
      complementRoot u ^ 2 = complementRatio u := by
    simpa [complementRoot] using Real.sq_sqrt (complementRatio_nonneg hu)
  have hsquare :
      (complementRoot u * (1 + u ^ 2)) ^ 2 =
        (Real.sqrt (1 - u ^ 4)) ^ 2 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hu_four)]
    unfold complementRatio at hv_sq
    rw [mul_pow, hv_sq]
    field_simp
    ring
  have hleft : 0 ≤ complementRoot u * (1 + u ^ 2) :=
    mul_nonneg hv.1 (by positivity)
  have hright : 0 ≤ Real.sqrt (1 - u ^ 4) :=
    Real.sqrt_nonneg _
  nlinarith [sq_nonneg
    (complementRoot u * (1 + u ^ 2) + Real.sqrt (1 - u ^ 4))]

private theorem sqrt_one_sub_complementRoot_four {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    Real.sqrt (1 - complementRoot u ^ 4) =
      2 * u / (1 + u ^ 2) := by
  have hu_closed : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  have hv := complementRoot_mem_Icc hu_closed
  have hv_sq :
      complementRoot u ^ 2 = complementRatio u := by
    simpa [complementRoot] using
      Real.sq_sqrt (complementRatio_nonneg hu_closed)
  have hv_sq_le : complementRoot u ^ 2 ≤ 1 :=
    (sq_le_one_iff₀ hv.1).2 hv.2
  have hv_four : complementRoot u ^ 4 ≤ 1 := by
    calc
      complementRoot u ^ 4 = (complementRoot u ^ 2) ^ 2 := by ring
      _ ≤ 1 := (sq_le_one_iff₀ (sq_nonneg (complementRoot u))).2 hv_sq_le
  have hsquare :
      (Real.sqrt (1 - complementRoot u ^ 4)) ^ 2 =
        (2 * u / (1 + u ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hv_four)]
    unfold complementRatio at hv_sq
    rw [show complementRoot u ^ 4 =
      (complementRoot u ^ 2) ^ 2 by ring, hv_sq]
    field_simp
    ring
  have hleft : 0 ≤ Real.sqrt (1 - complementRoot u ^ 4) :=
    Real.sqrt_nonneg _
  have hright : 0 ≤ 2 * u / (1 + u ^ 2) :=
    div_nonneg (mul_nonneg (by norm_num) hu.1.le) (by positivity)
  nlinarith [sq_nonneg
    (Real.sqrt (1 - complementRoot u ^ 4) + 2 * u / (1 + u ^ 2))]

private noncomputable def complementSum (u : ℝ) : ℝ :=
  arcsl u + arcsl (complementRoot u)

private theorem complementSum_hasDerivAt {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt complementSum 0 u := by
  have hv := complementRoot_mem_Ioo hu
  have hsecond :=
    (arcsl_hasDerivAt hv).comp u (complementRoot_hasDerivAt hu)
  have hraw :
      HasDerivAt complementSum
        (arcslIntegrand u +
          arcslIntegrand (complementRoot u) *
            (-2 * u / (complementRoot u * (1 + u ^ 2) ^ 2))) u := by
    simpa only [complementSum] using!
      (arcsl_hasDerivAt hu).add hsecond
  have hu_closed : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  have hzero :
      arcslIntegrand u +
          arcslIntegrand (complementRoot u) *
            (-2 * u / (complementRoot u * (1 + u ^ 2) ^ 2)) = 0 := by
    unfold arcslIntegrand
    rw [sqrt_one_sub_complementRoot_four hu,
      ← complementRoot_mul_one_add_sq hu_closed]
    have hu_ne : u ≠ 0 := hu.1.ne'
    have hv_ne : complementRoot u ≠ 0 := hv.1.ne'
    have hden_ne : 1 + u ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  simpa only [hzero] using hraw

private theorem complementSum_continuousOn :
    ContinuousOn complementSum (Icc (0 : ℝ) 1) := by
  have hcomp :
      ContinuousOn (fun u : ℝ => arcsl (complementRoot u))
        (Icc (0 : ℝ) 1) :=
    arcsl_continuousOn.comp complementRoot_continuous.continuousOn
      (fun u hu => complementRoot_mem_Icc hu)
  simpa only [complementSum] using! arcsl_continuousOn.add hcomp

private theorem complementSum_eq_half {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    complementSum u = varpi / 2 := by
  have hdiff :
      DifferentiableOn ℝ complementSum (Ioo (0 : ℝ) 1) :=
    fun x hx => (complementSum_hasDerivAt hx).differentiableAt.differentiableWithinAt
  have hderiv :
      (Ioo (0 : ℝ) 1).EqOn (deriv complementSum) 0 :=
    fun x hx => by
      simpa using (complementSum_hasDerivAt hx).deriv
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hinterior :
      (Ioo (0 : ℝ) 1).EqOn complementSum
        (fun _ : ℝ => complementSum (1 / 2)) := by
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hderiv hx hhalf
  have hclosure :
      Icc (0 : ℝ) 1 ⊆ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hall :=
    hinterior.of_subset_closure complementSum_continuousOn
      continuousOn_const Ioo_subset_Icc_self hclosure
  calc
    complementSum u = complementSum (1 / 2) := hall hu
    _ = complementSum 0 :=
      (hall (left_mem_Icc.2 zero_le_one)).symm
    _ = varpi / 2 := by
      simp [complementSum, complementRoot, complementRatio, arcsl_one]

theorem cl_eq_complementRoot {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (varpi / 2)) :
    cl x = complementRoot (sl x) := by
  have hu := sl_mem_Icc x
  have hsum := complementSum_eq_half hu
  unfold complementSum at hsum
  rw [arcsl_sl hx] at hsum
  have htarget : varpi / 2 - x ∈ Icc (0 : ℝ) (varpi / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hroot := complementRoot_mem_Icc hu
  have harg : arcsl (complementRoot (sl x)) = varpi / 2 - x := by
    linarith
  calc
    cl x = sl (varpi / 2 - x) := rfl
    _ = sl (arcsl (complementRoot (sl x))) := by rw [harg]
    _ = complementRoot (sl x) := sl_arcsl hroot

theorem cl_sq_eq {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (varpi / 2)) :
    cl x ^ 2 = (1 - sl x ^ 2) / (1 + sl x ^ 2) := by
  rw [cl_eq_complementRoot hx]
  simpa [complementRoot, complementRatio] using
    Real.sq_sqrt (complementRatio_nonneg (sl_mem_Icc x))

theorem cl_sl_algebra {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (varpi / 2)) :
    cl x ^ 2 + sl x ^ 2 + cl x ^ 2 * sl x ^ 2 = 1 := by
  have hden : 1 + sl x ^ 2 ≠ 0 := by positivity
  have hsq := cl_sq_eq hx
  field_simp [hden] at hsq
  nlinarith

end LemniAcc.Lemniscatic
