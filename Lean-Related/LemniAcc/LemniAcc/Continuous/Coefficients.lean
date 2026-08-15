import LemniAcc.Lemniscatic.Calculus

open scoped Topology
open Set Filter

set_option autoImplicit false

namespace LemniAcc.Lemniscatic

theorem scaledAngle_hasDerivAt {T t : ℝ} (hT : T ≠ 0) :
    HasDerivAt (scaledAngle T) (varpiT T / 2) t := by
  have hcoef : varpiT T / 2 = varpi / (2 * T) := by
    unfold varpiT
    field_simp
  rw [hcoef]
  change HasDerivAt (fun x : ℝ => varpi * x / (2 * T))
    (varpi / (2 * T)) t
  simpa only [mul_one] using!
    ((hasDerivAt_id' t).const_mul varpi).div_const (2 * T)

theorem scaledAngle_mem_Ioo {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    scaledAngle T t ∈ Ioo (0 : ℝ) (varpi / 2) := by
  have hden : 0 < 2 * T := mul_pos (by norm_num) hT
  constructor
  · exact div_pos (mul_pos varpi_pos ht.1) hden
  · calc
      varpi * t / (2 * T) < varpi * T / (2 * T) :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_left ht.2 varpi_pos) hden
      _ = varpi / 2 := by field_simp [hT.ne']

theorem scaledAngle_mem_Icc {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc (0 : ℝ) T) :
    scaledAngle T t ∈ Icc (0 : ℝ) (varpi / 2) := by
  have hden : 0 < 2 * T := mul_pos (by norm_num) hT
  constructor
  · exact div_nonneg (mul_nonneg varpi_pos.le ht.1) hden.le
  · calc
      varpi * t / (2 * T) ≤ varpi * T / (2 * T) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left ht.2 varpi_pos.le) hden.le
      _ = varpi / 2 := by field_simp [hT.ne']

theorem scaledAngle_reflection {T t : ℝ} (hT : T ≠ 0) :
    scaledAngle T (T - t) = varpi / 2 - scaledAngle T t := by
  unfold scaledAngle
  field_simp

theorem varpiT_pos {T : ℝ} (hT : 0 < T) :
    0 < varpiT T :=
  div_pos varpi_pos hT

theorem scaledAngle_eq_varpiT_mul {T t : ℝ} :
    scaledAngle T t = varpiT T / 2 * t := by
  unfold scaledAngle varpiT
  ring

theorem scaledAngle_tendsto_nhdsGT_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (scaledAngle T) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont :
        Tendsto (scaledAngle T) (𝓝 (0 : ℝ))
          (𝓝 (scaledAngle T 0)) :=
      (by
        unfold scaledAngle
        fun_prop : Continuous (scaledAngle T)).continuousAt
    change Tendsto (scaledAngle T)
      (𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi 0)) (𝓝 (0 : ℝ))
    simpa [scaledAngle] using hcont.mono_left inf_le_left
  · filter_upwards [eventually_mem_nhdsWithin] with t ht
    rw [scaledAngle_eq_varpiT_mul]
    exact mul_pos (div_pos (varpiT_pos hT) (by norm_num)) ht

theorem rho_pos_lt_one {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < rho T t ∧ rho T t < 1 := by
  have hc := cl_mem_Ioo (scaledAngle_mem_Ioo hT ht)
  constructor
  · exact sq_pos_of_pos hc.1
  · exact (sq_lt_one_iff₀ hc.1.le).2 hc.2

theorem rho_reflection {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc (0 : ℝ) T) :
    rho T (T - t) = (1 - rho T t) / (1 + rho T t) := by
  have ha := scaledAngle_mem_Icc hT ht
  have halg := cl_sl_algebra ha
  simp only [rho, Pi.pow_apply, Function.comp_apply]
  rw [scaledAngle_reflection hT.ne', cl_complement]
  have hden : 1 + cl (scaledAngle T t) ^ 2 ≠ 0 := by positivity
  field_simp
  nlinarith [halg]

theorem rho_terminal_eq_sl_sq {T delta : ℝ} (hT : T ≠ 0) :
    rho T (T - delta) = sl (scaledAngle T delta) ^ 2 := by
  simp only [rho, Pi.pow_apply, Function.comp_apply]
  rw [scaledAngle_reflection hT, cl_complement]

theorem rho_continuous (T : ℝ) :
    Continuous (rho T) := by
  unfold rho
  apply Continuous.pow
  exact cl_continuous.comp (by
    unfold scaledAngle
    fun_prop)

@[simp] theorem rho_zero (T : ℝ) :
    rho T 0 = 1 := by
  simp [rho, scaledAngle]

theorem rho_horizon {T : ℝ} (hT : T ≠ 0) :
    rho T T = 0 := by
  have hangle : scaledAngle T T = varpi / 2 := by
    unfold scaledAngle
    field_simp
  simp [rho, hangle]

theorem rho_terminal_tendsto_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (fun delta : ℝ => rho T (T - delta))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hid :
      Tendsto (fun delta : ℝ => delta)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left inf_le_left
  have hinner :
      Tendsto (fun delta : ℝ => T - delta)
        (𝓝[>] (0 : ℝ)) (𝓝 T) := by
    simpa using tendsto_const_nhds.sub hid
  simpa [Function.comp_def, rho_horizon hT.ne'] using
    (rho_continuous T).continuousAt.tendsto.comp hinner

theorem rho_terminal_normalized_tendsto {T : ℝ} (hT : 0 < T) :
    Tendsto (fun delta : ℝ => rho T (T - delta) / delta ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (varpiT T ^ 2 / 4)) := by
  let c : ℝ := varpiT T / 2
  have hc : 0 < c := div_pos (varpiT_pos hT) (by norm_num)
  have hratio :
      Tendsto
        (fun delta : ℝ =>
          sl (scaledAngle T delta) / scaledAngle T delta)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
    sl_div_tendsto_one.comp (scaledAngle_tendsto_nhdsGT_zero hT)
  have hmodel :
      Tendsto
        (fun delta : ℝ =>
          (sl (scaledAngle T delta) / scaledAngle T delta) ^ 2 *
            c ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℝ) ^ 2 * c ^ 2)) :=
    (hratio.pow 2).mul tendsto_const_nhds
  have heq :
      (fun delta : ℝ =>
        (sl (scaledAngle T delta) / scaledAngle T delta) ^ 2 *
          c ^ 2) =ᶠ[𝓝[>] (0 : ℝ)]
        fun delta : ℝ => rho T (T - delta) / delta ^ 2 := by
    filter_upwards [eventually_mem_nhdsWithin] with delta hdelta
    have hdelta0 : delta ≠ 0 := ne_of_gt hdelta
    rw [rho_terminal_eq_sl_sq hT.ne',
      scaledAngle_eq_varpiT_mul]
    change
      (sl (c * delta) / (c * delta)) ^ 2 * c ^ 2 =
        sl (c * delta) ^ 2 / delta ^ 2
    field_simp [hc.ne', hdelta0]
  have hlimit := hmodel.congr' heq
  have hconst : c ^ 2 = varpiT T ^ 2 / 4 := by
    dsimp [c]
    ring
  rw [← hconst]
  simpa using hlimit

theorem sigma_pos {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < sigma T t := by
  have hr := rho_pos_lt_one hT ht
  unfold sigma
  apply Real.sqrt_pos.2
  exact div_pos (by nlinarith [sq_nonneg (rho T t)]) hr.1

theorem sigma_sq {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    sigma T t ^ 2 = (1 - rho T t ^ 2) / rho T t := by
  unfold sigma
  apply Real.sq_sqrt
  have hr := rho_pos_lt_one hT ht
  exact div_nonneg (by nlinarith [sq_nonneg (rho T t)]) hr.1.le

theorem sigma_sq_eq_inv_sub {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    sigma T t ^ 2 = (rho T t)⁻¹ - rho T t := by
  rw [sigma_sq hT ht]
  have hr := (rho_pos_lt_one hT ht).1.ne'
  field_simp

theorem sigma_terminal_normalized_tendsto {T : ℝ} (hT : 0 < T) :
    Tendsto (fun delta : ℝ => delta * sigma T (T - delta))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / varpiT T)) := by
  let c : ℝ := varpiT T / 2
  have hc : 0 < c := div_pos (varpiT_pos hT) (by norm_num)
  have hr0 := rho_terminal_tendsto_zero hT
  have hrn :
      Tendsto (fun delta : ℝ => rho T (T - delta) / delta ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (c ^ 2)) := by
    have h := rho_terminal_normalized_tendsto hT
    have hconst : varpiT T ^ 2 / 4 = c ^ 2 := by
      dsimp [c]
      ring
    simpa [hconst] using h
  have hnum :
      Tendsto (fun delta : ℝ => 1 - rho T (T - delta) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (hr0.pow 2)
  have hrad :
      Tendsto
        (fun delta : ℝ =>
          (1 - rho T (T - delta) ^ 2) /
            (rho T (T - delta) / delta ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / c ^ 2)) := by
    have hdiv :=
      hnum.div hrn (pow_ne_zero 2 hc.ne')
    have heq :
        ((fun delta : ℝ => 1 - rho T (T - delta) ^ 2) /
          fun delta : ℝ => rho T (T - delta) / delta ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)]
        fun delta : ℝ =>
          (1 - rho T (T - delta) ^ 2) /
            (rho T (T - delta) / delta ^ 2) :=
      Eventually.of_forall fun delta => by
        rw [Pi.div_apply]
    simpa only [one_div] using hdiv.congr' heq
  have hsqrt :
      Tendsto
        (fun delta : ℝ =>
          Real.sqrt
            ((1 - rho T (T - delta) ^ 2) /
              (rho T (T - delta) / delta ^ 2)))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (1 / c ^ 2))) :=
    (Real.continuous_sqrt.continuousAt.tendsto).comp hrad
  have heq :
      (fun delta : ℝ => delta * sigma T (T - delta)) =ᶠ[𝓝[>] (0 : ℝ)]
        fun delta : ℝ =>
          Real.sqrt
            ((1 - rho T (T - delta) ^ 2) /
              (rho T (T - delta) / delta ^ 2)) := by
    have hlt :
        ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), delta < T := by
      have hlt' : ∀ᶠ delta : ℝ in 𝓝 (0 : ℝ), delta < T :=
        Iio_mem_nhds hT
      exact hlt'.filter_mono inf_le_left
    filter_upwards [eventually_mem_nhdsWithin, hlt] with delta hdelta hdeltaT
    have hdeltaPos : 0 < delta := hdelta
    have ht : T - delta ∈ Ioo (0 : ℝ) T := by
      constructor <;> linarith
    have hr := rho_pos_lt_one hT ht
    unfold sigma
    calc
      delta *
          Real.sqrt
            ((1 - rho T (T - delta) ^ 2) / rho T (T - delta)) =
          Real.sqrt (delta ^ 2) *
            Real.sqrt
              ((1 - rho T (T - delta) ^ 2) / rho T (T - delta)) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hdeltaPos]
      _ = Real.sqrt
          (delta ^ 2 *
            ((1 - rho T (T - delta) ^ 2) /
              rho T (T - delta))) := by
            rw [Real.sqrt_mul (sq_nonneg delta)]
      _ = Real.sqrt
          ((1 - rho T (T - delta) ^ 2) /
            (rho T (T - delta) / delta ^ 2)) := by
            congr 1
            field_simp [hr.1.ne', hdeltaPos.ne']
  have hsqrtConst :
      Real.sqrt (1 / c ^ 2) = 1 / c := by
    rw [show 1 / c ^ 2 = (1 / c) ^ 2 by
      field_simp [hc.ne'],
      Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hc)]
  have hscale : 1 / c = 2 / varpiT T := by
    dsimp [c]
    field_simp [(varpiT_pos hT).ne']
  rw [← hscale, ← hsqrtConst]
  exact hsqrt.congr' heq.symm

theorem sigma_terminal_inv_tendsto_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (fun delta : ℝ => (sigma T (T - delta))⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hdelta :
      Tendsto (fun delta : ℝ => delta)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left inf_le_left
  have hsigma := sigma_terminal_normalized_tendsto hT
  have hscale : 2 / varpiT T ≠ 0 :=
    div_ne_zero (by norm_num) (varpiT_pos hT).ne'
  have hdiv :=
    hdelta.div hsigma hscale
  have hquot :
      Tendsto
        (fun delta : ℝ =>
          delta / (delta * sigma T (T - delta)))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have heq :
        ((fun delta : ℝ => delta) /
          fun delta : ℝ => delta * sigma T (T - delta))
          =ᶠ[𝓝[>] (0 : ℝ)]
        fun delta : ℝ =>
          delta / (delta * sigma T (T - delta)) :=
      Eventually.of_forall fun delta => by rw [Pi.div_apply]
    simpa using hdiv.congr' heq
  apply hquot.congr'
  have hlt :
      ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), delta < T := by
    have hlt' : ∀ᶠ delta : ℝ in 𝓝 (0 : ℝ), delta < T :=
      Iio_mem_nhds hT
    exact hlt'.filter_mono inf_le_left
  filter_upwards [eventually_mem_nhdsWithin, hlt] with delta hdeltaPos hdeltaT
  have ht : T - delta ∈ Ioo (0 : ℝ) T := by
    constructor <;> linarith [show 0 < delta from hdeltaPos]
  have hsne := (sigma_pos hT ht).ne'
  field_simp [ne_of_gt (show 0 < delta from hdeltaPos), hsne]

theorem gamma_terminal_normalized_tendsto {T : ℝ} (hT : 0 < T) :
    Tendsto (fun delta : ℝ => delta * gamma T (T - delta))
      (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℝ)) := by
  let v : ℝ := varpiT T
  have hv : 0 < v := by simpa [v] using varpiT_pos hT
  have hdelta :
      Tendsto (fun delta : ℝ => delta)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left inf_le_left
  have hrho := rho_terminal_tendsto_zero hT
  have hinv := sigma_terminal_inv_tendsto_zero hT
  have hdeltaRho :
      Tendsto (fun delta : ℝ => delta * rho T (T - delta))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Pi.mul_apply, zero_mul] using hdelta.mul hrho
  have hsmall0 :
      Tendsto
        (fun delta : ℝ =>
          delta * rho T (T - delta) *
            (sigma T (T - delta))⁻¹)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Pi.mul_apply, zero_mul] using hdeltaRho.mul hinv
  have hsmall :
      Tendsto
        (fun delta : ℝ =>
          2 * delta * rho T (T - delta) /
            sigma T (T - delta))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have htwo :
        Tendsto (fun _delta : ℝ => (2 : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    have h := htwo.mul hsmall0
    simpa only [Pi.mul_apply, div_eq_mul_inv, zero_mul, mul_zero,
      mul_assoc] using h
  have hsigma :
      Tendsto (fun delta : ℝ => delta * sigma T (T - delta))
        (𝓝[>] (0 : ℝ)) (𝓝 (2 / v)) := by
    simpa [v] using sigma_terminal_normalized_tendsto hT
  have hmodel :
      Tendsto
        (fun delta : ℝ =>
          3 * (v / 2) *
            (delta * sigma T (T - delta) +
              2 * delta * rho T (T - delta) /
                sigma T (T - delta)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (3 * (v / 2) * (2 / v + 0))) := by
    simpa only [Pi.mul_apply, Pi.add_apply] using
      tendsto_const_nhds.mul (hsigma.add hsmall)
  have heq :
      (fun delta : ℝ => delta * gamma T (T - delta))
        =ᶠ[𝓝[>] (0 : ℝ)]
      fun delta : ℝ =>
        3 * (v / 2) *
          (delta * sigma T (T - delta) +
            2 * delta * rho T (T - delta) /
              sigma T (T - delta)) := by
    have hlt :
        ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), delta < T := by
      have hlt' : ∀ᶠ delta : ℝ in 𝓝 (0 : ℝ), delta < T :=
        Iio_mem_nhds hT
      exact hlt'.filter_mono inf_le_left
    filter_upwards [eventually_mem_nhdsWithin, hlt] with delta hdelta hdeltaT
    have ht : T - delta ∈ Ioo (0 : ℝ) T := by
      constructor <;> linarith [show 0 < delta from hdelta]
    let r : ℝ := rho T (T - delta)
    let s : ℝ := sigma T (T - delta)
    have hs2 : s ^ 2 = r⁻¹ - r := by
      simpa [s, r] using sigma_sq_eq_inv_sub hT ht
    have hsum : r + r⁻¹ = s ^ 2 + 2 * r := by
      rw [hs2]
      ring
    have hsne : s ≠ 0 := by
      simpa [s] using (sigma_pos hT ht).ne'
    unfold gamma sigmaDot
    change
      delta * (3 * (v / 2 * (r + r⁻¹)) / s) =
        3 * (v / 2) *
          (delta * s + 2 * delta * r / s)
    rw [hsum]
    field_simp [hsne]
  have hlimit := hmodel.congr' heq.symm
  have hconst : 3 * (v / 2) * (2 / v + 0) = (3 : ℝ) := by
    field_simp [hv.ne']
    ring
  rw [hconst] at hlimit
  exact hlimit

theorem sqrt_rho_mul_one_sub_sq {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    Real.sqrt (rho T t * (1 - rho T t ^ 2)) =
      cl (scaledAngle T t) *
        Real.sqrt (1 - cl (scaledAngle T t) ^ 4) := by
  have hc := cl_mem_Ioo (scaledAngle_mem_Ioo hT ht)
  simp only [rho, Pi.pow_apply, Function.comp_apply]
  rw [show cl (scaledAngle T t) ^ 2 *
      (1 - (cl (scaledAngle T t) ^ 2) ^ 2) =
      cl (scaledAngle T t) ^ 2 *
        (1 - cl (scaledAngle T t) ^ 4) by ring,
    Real.sqrt_mul (sq_nonneg (cl (scaledAngle T t))),
    Real.sqrt_sq_eq_abs, abs_of_pos hc.1]

theorem sigma_mul_rho {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    sigma T t * rho T t =
      Real.sqrt (rho T t * (1 - rho T t ^ 2)) := by
  have hr := rho_pos_lt_one hT ht
  have hs := sigma_pos hT ht
  have hsq := sigma_sq hT ht
  have hrad : 0 ≤ rho T t * (1 - rho T t ^ 2) :=
    mul_nonneg hr.1.le (by nlinarith [sq_nonneg (rho T t)])
  have hsquare :
      (sigma T t * rho T t) ^ 2 =
        (Real.sqrt (rho T t * (1 - rho T t ^ 2))) ^ 2 := by
    rw [Real.sq_sqrt hrad, mul_pow, hsq]
    field_simp [hr.1.ne']
  have hleft : 0 ≤ sigma T t * rho T t :=
    mul_nonneg hs.le hr.1.le
  have hright : 0 ≤ Real.sqrt
      (rho T t * (1 - rho T t ^ 2)) :=
    Real.sqrt_nonneg _
  nlinarith [sq_nonneg
    (sigma T t * rho T t +
      Real.sqrt (rho T t * (1 - rho T t ^ 2)))]

theorem rho_hasDerivAt {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (rho T)
      (-varpiT T *
        Real.sqrt (rho T t * (1 - rho T t ^ 2))) t := by
  have ha := scaledAngle_mem_Ioo hT ht
  have hcomp :=
    (cl_hasDerivAt ha).comp t (scaledAngle_hasDerivAt hT.ne')
  have hpow :
      HasDerivAt (rho T)
        (-(2 * cl (scaledAngle T t) *
          (Real.sqrt (1 - cl (scaledAngle T t) ^ 4) *
            (varpiT T / 2)))) t := by
    simpa [rho] using! hcomp.pow 2
  have hraw :
      HasDerivAt (rho T)
        (-varpiT T * cl (scaledAngle T t) *
          Real.sqrt (1 - cl (scaledAngle T t) ^ 4)) t := by
    convert hpow using 1
    ring
  rw [sqrt_rho_mul_one_sub_sq hT ht]
  simpa only [mul_assoc] using hraw

theorem rho_hasDerivAt_sigma {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (rho T) (-varpiT T * sigma T t * rho T t) t := by
  have h := rho_hasDerivAt hT ht
  rw [← sigma_mul_rho hT ht] at h
  simpa only [mul_assoc] using h

theorem sigma_hasDerivAt {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (sigma T) (sigmaDot T t) t := by
  let r : ℝ := rho T t
  let s : ℝ := sigma T t
  let rp : ℝ := -varpiT T * s * r
  have hr : 0 < r := by
    simpa [r] using (rho_pos_lt_one hT ht).1
  have hs : 0 < s := by simpa [s] using sigma_pos hT ht
  have hrd : HasDerivAt (rho T) rp t := by
    simpa [rp, r, s] using rho_hasDerivAt_sigma hT ht
  have hnum :
      HasDerivAt (fun u : ℝ => 1 - rho T u ^ 2)
        (-2 * r * rp) t := by
    simpa [r] using! (hrd.pow 2).const_sub 1
  have hquot :
      HasDerivAt (fun u : ℝ =>
        (1 - rho T u ^ 2) / rho T u)
        (((-2 * r * rp) * r - (1 - r ^ 2) * rp) / r ^ 2) t := by
    simpa [r] using! hnum.div hrd hr.ne'
  have hqpos :
      0 < (1 - rho T t ^ 2) / rho T t := by
    exact div_pos
      (by nlinarith [sq_nonneg (rho T t), (rho_pos_lt_one hT ht).2])
      (rho_pos_lt_one hT ht).1
  have hsraw :
      HasDerivAt (sigma T)
        ((((-2 * r * rp) * r - (1 - r ^ 2) * rp) / r ^ 2) /
          (2 * s)) t := by
    change HasDerivAt
      (fun u : ℝ => Real.sqrt ((1 - rho T u ^ 2) / rho T u))
      ((((-2 * r * rp) * r - (1 - r ^ 2) * rp) / r ^ 2) /
        (2 * s)) t
    simpa [sigma, s] using! hquot.sqrt hqpos.ne'
  have hcoef :
      (((-2 * r * rp) * r - (1 - r ^ 2) * rp) / r ^ 2) /
          (2 * s) =
        sigmaDot T t := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hs.ne')).2
    apply (div_eq_iff (pow_ne_zero 2 hr.ne')).2
    unfold sigmaDot
    dsimp [rp, r, s]
    field_simp [hr.ne']
    ring
  rw [← hcoef]
  exact hsraw

theorem sigmaDot_hasDerivAt {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (sigmaDot T)
      (varpiT T ^ 2 / 2 * sigma T t ^ 3) t := by
  let r : ℝ := rho T t
  let s : ℝ := sigma T t
  let rp : ℝ := -varpiT T * s * r
  have hr : 0 < r := by
    simpa [r] using (rho_pos_lt_one hT ht).1
  have hrd : HasDerivAt (rho T) rp t := by
    simpa [rp, r, s] using rho_hasDerivAt_sigma hT ht
  have hsum :
      HasDerivAt (fun u : ℝ => rho T u + (rho T u)⁻¹)
        (rp + (-rp / r ^ 2)) t := by
    simpa [r] using! hrd.add (hrd.inv hr.ne')
  have hraw :
      HasDerivAt (sigmaDot T)
        (varpiT T / 2 * (rp + (-rp / r ^ 2))) t := by
    simpa [sigmaDot] using!
      hsum.const_mul (varpiT T / 2)
  have hs2 : s ^ 2 = r⁻¹ - r := by
    simpa [s, r] using sigma_sq_eq_inv_sub hT ht
  have hcoef :
      varpiT T / 2 * (rp + (-rp / r ^ 2)) =
        varpiT T ^ 2 / 2 * s ^ 3 := by
    calc
      varpiT T / 2 * (rp + (-rp / r ^ 2)) =
          varpiT T ^ 2 / 2 * s * (r⁻¹ - r) := by
            dsimp [rp]
            field_simp [hr.ne']
            ring
      _ = varpiT T ^ 2 / 2 * s * s ^ 2 := by rw [← hs2]
      _ = varpiT T ^ 2 / 2 * s ^ 3 := by ring
  rw [← hcoef]
  simpa [s] using hraw

theorem sigma_mul_reflection {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    sigma T t * sigma T (T - t) = 2 := by
  have href : T - t ∈ Ioo (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2]
  have htcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  let r : ℝ := rho T t
  let q : ℝ := rho T (T - t)
  have hr : 0 < r ∧ r < 1 := by
    simpa [r] using rho_pos_lt_one hT ht
  have hq : 0 < q ∧ q < 1 := by
    simpa [q] using rho_pos_lt_one hT href
  have hreflect : q = (1 - r) / (1 + r) := by
    simpa [q, r] using rho_reflection hT htcc
  have h1pr : 1 + r ≠ 0 := by nlinarith [hr.1]
  have h1mr : 1 - r ≠ 0 := by nlinarith [hr.2]
  have hrSq : r ^ 2 < 1 := (sq_lt_one_iff₀ hr.1.le).2 hr.2
  have h1mrSq : 1 - r ^ 2 ≠ 0 := by nlinarith
  have hqterm :
      (1 - q ^ 2) / q = 4 * r / (1 - r ^ 2) := by
    rw [hreflect]
    field_simp [h1pr, h1mr]
    ring
  have hsqt :
      sigma T t ^ 2 = (1 - r ^ 2) / r := by
    simpa [r] using sigma_sq hT ht
  have hsqref :
      sigma T (T - t) ^ 2 = (1 - q ^ 2) / q := by
    simpa [q] using sigma_sq hT href
  have hprodSq :
      (sigma T t * sigma T (T - t)) ^ 2 = 4 := by
    rw [mul_pow, hsqt, hsqref, hqterm]
    field_simp [hr.1.ne', h1mrSq]
  have hprodPos :
      0 < sigma T t * sigma T (T - t) :=
    mul_pos (sigma_pos hT ht) (sigma_pos hT href)
  nlinarith

theorem gamma_reflection {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    gamma T (T - t) = gamma T t := by
  have href : T - t ∈ Ioo (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2]
  let r : ℝ := rho T t
  let q : ℝ := rho T (T - t)
  let s : ℝ := sigma T t
  let sr : ℝ := sigma T (T - t)
  have hr : 0 < r ∧ r < 1 := by
    simpa [r] using rho_pos_lt_one hT ht
  have hq : 0 < q ∧ q < 1 := by
    simpa [q] using rho_pos_lt_one hT href
  have hs : 0 < s := by simpa [s] using sigma_pos hT ht
  have hsr : 0 < sr := by simpa [sr] using sigma_pos hT href
  have hreflect : q = (1 - r) / (1 + r) := by
    simpa [q, r] using
      rho_reflection hT ⟨ht.1.le, ht.2.le⟩
  have hprod : s * sr = 2 := by
    simpa [s, sr] using sigma_mul_reflection hT ht
  have hs2 : s ^ 2 = r⁻¹ - r := by
    simpa [s, r] using sigma_sq_eq_inv_sub hT ht
  have hs2poly : s ^ 2 * r = 1 - r ^ 2 := by
    rw [hs2]
    field_simp [hr.1.ne']
  have h1pr : 1 + r ≠ 0 := by nlinarith [hr.1]
  have h1mr : 1 - r ≠ 0 := by nlinarith [hr.2]
  have h1mrSq : 1 - r ^ 2 ≠ 0 := by
    have hrsq : r ^ 2 < 1 := (sq_lt_one_iff₀ hr.1.le).2 hr.2
    nlinarith
  have hqsum :
      q + q⁻¹ = 2 * (1 + r ^ 2) / (1 - r ^ 2) := by
    rw [hreflect]
    field_simp [h1pr, h1mr]
    ring
  have hrsum : r + r⁻¹ = (1 + r ^ 2) / r := by
    field_simp [hr.1.ne']
    ring
  have hquot :
      (q + q⁻¹) / sr = (r + r⁻¹) / s := by
    rw [hqsum, hrsum]
    field_simp [hs.ne', hsr.ne', hr.1.ne', h1mrSq]
    rw [← hs2poly]
    nlinarith [hprod]
  unfold gamma sigmaDot
  change
    3 * (varpiT T / 2 * (q + q⁻¹)) / sr =
      3 * (varpiT T / 2 * (r + r⁻¹)) / s
  calc
    3 * (varpiT T / 2 * (q + q⁻¹)) / sr =
        3 * (varpiT T / 2) * ((q + q⁻¹) / sr) := by ring
    _ = 3 * (varpiT T / 2) * ((r + r⁻¹) / s) := by
      rw [hquot]
    _ = 3 * (varpiT T / 2 * (r + r⁻¹)) / s := by ring

theorem gamma_initial_normalized_tendsto {T : ℝ} (hT : 0 < T) :
    Tendsto (fun t : ℝ => t * gamma T t)
      (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℝ)) := by
  have hterminal := gamma_terminal_normalized_tendsto hT
  apply hterminal.congr'
  have hlt :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < T := by
    have hlt' : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < T :=
      Iio_mem_nhds hT
    exact hlt'.filter_mono inf_le_left
  filter_upwards [eventually_mem_nhdsWithin, hlt] with t ht hTt
  rw [gamma_reflection hT ⟨ht, hTt⟩]

theorem gamma_eq_three_mul_sigmaDot_div_sigma {T t : ℝ} :
    gamma T t = 3 * sigmaDot T t / sigma T t := rfl

end LemniAcc.Lemniscatic

namespace LemniAcc.Internal

open Lemniscatic

/-- The complete lemniscatic-calculus and continuous-coefficient certificate
used by the continuous-time argument. -/
theorem sigma_identities (T : ℝ) (hT : 0 < T) :
    Lemniscatic.SigmaIdentities T := by
  refine
    { horizon_pos := hT
      sl_continuous_on_real := sl_continuous
      sl_strict_increasing := sl_strictMonoOn
      sl_bijection :=
        ⟨sl_mapsTo, sl_strictMonoOn.injOn, sl_surjOn⟩
      sl_endpoints := ⟨sl_zero, sl_varpi_half⟩
      cl_continuous_on_real := cl_continuous
      cl_strict_decreasing := cl_strictAntiOn
      cl_bijection :=
        ⟨(fun x _ => cl_mem_Icc x), cl_strictAntiOn.injOn, cl_surjOn⟩
      cl_endpoints := ⟨cl_zero, cl_varpi_half⟩
      interior_values := fun hx => ⟨sl_mem_Ioo hx, cl_mem_Ioo hx⟩
      sl_derivative := fun hx => sl_hasDerivAt hx
      cl_derivative := fun hx => cl_hasDerivAt hx
      complement_identity := fun _ => cl_complement _
      complement_square := fun hx => cl_sq_eq hx
      complement_algebra := fun hx => cl_sl_algebra hx
      sl_first_order := sl_sub_id_isLittleO
      rho_interior := fun ht => rho_pos_lt_one hT ht
      rho_symmetry := fun ht => rho_reflection hT ht
      rho_derivative_root := fun ht => rho_hasDerivAt hT ht
      rho_derivative_sigma := fun ht => rho_hasDerivAt_sigma hT ht
      sigma_derivative := fun ht => sigma_hasDerivAt hT ht
      sigma_second_derivative := fun ht => sigmaDot_hasDerivAt hT ht
      sigma_reflection := fun ht => sigma_mul_reflection hT ht }

end LemniAcc.Internal
