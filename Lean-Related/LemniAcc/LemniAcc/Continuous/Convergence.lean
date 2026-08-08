import LemniAcc.Continuous.Lyapunov

/-!
# Endpoint limits and continuous-time rates for LemniAcc

This module derives both endpoint limits of the continuous Lyapunov function
from the closed-interval trajectory interface, then combines those limits with
interior monotonicity to obtain the manuscript's stronger endpoint inequality
and its two stated consequences.
-/

open scoped InnerProductSpace Topology
open Set Filter
open InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

open Lemniscatic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

namespace Continuous

/-- The continuous Lyapunov function is nonincreasing on the open time
interval. -/
theorem lyapunov_antitoneOn
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    AntitoneOn (lyapunov M T xStar x0 P) (Ioo (0 : ℝ) T) := by
  have hdiff :
      DifferentiableOn ℝ (lyapunov M T xStar x0 P)
        (Ioo (0 : ℝ) T) :=
    fun t ht =>
      (lyapunov_hasDerivAt xStar P hT ht).differentiableAt
        |>.differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos (convex_Ioo (0 : ℝ) T)
  · exact hdiff.continuousOn
  · simpa only [interior_Ioo] using hdiff
  · intro t ht
    exact lyapunov_deriv_nonpos xStar P hT
      (by simpa only [interior_Ioo] using ht)

private theorem initial_rho_tendsto
    {T : ℝ} :
    Tendsto (rho T) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  have h :
      Tendsto (rho T) (𝓝 (0 : ℝ)) (𝓝 (rho T 0)) :=
    (rho_continuous T).continuousAt.tendsto
  have h' := h.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  simpa using h'

private theorem initial_sigma_tendsto
    {T : ℝ} :
    Tendsto (sigma T) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hr := initial_rho_tendsto (T := T)
  have hone :
      Tendsto (fun _t : ℝ => (1 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hrad :
      Tendsto
        (fun t : ℝ => (1 - rho T t ^ 2) / rho T t)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (hone.sub (hr.pow 2)).div hr (by norm_num)
    norm_num at h
    apply h.congr'
    exact Filter.Eventually.of_forall fun t => rfl
  have hsqrt :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hrad
  norm_num at hsqrt
  unfold sigma
  apply hsqrt.congr'
  exact Filter.Eventually.of_forall fun t => rfl

private theorem initial_terminalFunctionCoeff_tendsto
    {T : ℝ} :
    Tendsto (terminalFunctionCoeff T)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hr := initial_rho_tendsto (T := T)
  have hone :
      Tendsto (fun _t : ℝ => (1 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have htwo :
      Tendsto (fun _t : ℝ => (2 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) :=
    tendsto_const_nhds
  have hnum := (hone.sub hr).pow 2
  have hden := htwo.mul hr
  have h := hnum.div hden (by norm_num)
  norm_num at h
  unfold terminalFunctionCoeff
  apply h.congr'
  exact Filter.Eventually.of_forall fun t => rfl

private theorem trajectory_initial_position_tendsto
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    Tendsto P.X (𝓝[>] (0 : ℝ)) (𝓝 x0) := by
  have hcont :=
    (P.X_continuous 0 ⟨le_rfl, hT.le⟩).mono
      Ioo_subset_Icc_self
  simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hT,
    P.X_zero] using hcont

private theorem trajectory_initial_velocity_tendsto
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    Tendsto P.V (𝓝[>] (0 : ℝ)) (𝓝 (0 : E)) := by
  have hcont :=
    (P.V_continuous 0 ⟨le_rfl, hT.le⟩).mono
      Ioo_subset_Icc_self
  simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hT,
    P.V_zero] using hcont

/-- The rigorously derived initial endpoint limit of the Lyapunov function. -/
theorem lyapunov_initial_limit
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    Tendsto (lyapunov M T xStar x0 P)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((varpiT T ^ 2 / 2) *
        (‖x0 - xStar‖ ^ 2 - ‖P.X T - xStar‖ ^ 2))) := by
  have hr := initial_rho_tendsto (T := T)
  have hs := initial_sigma_tendsto (T := T)
  have hb := initial_terminalFunctionCoeff_tendsto (T := T)
  have hX := trajectory_initial_position_tendsto P hT
  have hV := trajectory_initial_velocity_tendsto P hT
  have hfX :
      Tendsto (fun t : ℝ => M.f (P.X t))
        (𝓝[>] (0 : ℝ)) (𝓝 (M.f x0)) :=
    (M.hasGradient x0).continuousAt.tendsto.comp hX
  have hU :
      Tendsto (fun t : ℝ => P.X t - xStar)
        (𝓝[>] (0 : ℝ)) (𝓝 (x0 - xStar)) :=
    hX.sub tendsto_const_nhds
  have hXT :
      Tendsto (fun t : ℝ => P.X t - P.X T)
        (𝓝[>] (0 : ℝ)) (𝓝 (x0 - P.X T)) :=
    hX.sub tendsto_const_nhds
  have hinnerU :
      Tendsto (fun t : ℝ => ⟪P.X t - xStar, P.V t⟫_ℝ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := Filter.Tendsto.inner (𝕜 := ℝ) hU hV
    simpa using h
  have hinnerT :
      Tendsto (fun t : ℝ => ⟪P.X t - P.X T, P.V t⟫_ℝ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := Filter.Tendsto.inner (𝕜 := ℝ) hXT hV
    simpa using h
  have h1 :
      Tendsto
        (fun t : ℝ =>
          (1 - rho T t) * (M.f (P.X t) - M.f xStar))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hone :
        Tendsto (fun _t : ℝ => (1 : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have hfstar :
        Tendsto (fun _t : ℝ => M.f xStar)
          (𝓝[>] (0 : ℝ)) (𝓝 (M.f xStar)) :=
      tendsto_const_nhds
    have hraw := (hone.sub hr).mul (hfX.sub hfstar)
    norm_num at hraw
    exact hraw
  have h2 :
      Tendsto
        (fun t : ℝ =>
          terminalFunctionCoeff T t *
            (M.f (P.X t) - M.f (P.X T)))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Pi.mul_apply, zero_mul] using
      hb.mul (hfX.sub tendsto_const_nhds)
  have h3 :
      Tendsto
        (fun t : ℝ =>
          (varpiT T ^ 2 / 2) *
            (‖P.X t - xStar‖ ^ 2 - ‖P.X T - xStar‖ ^ 2))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((varpiT T ^ 2 / 2) *
          (‖x0 - xStar‖ ^ 2 - ‖P.X T - xStar‖ ^ 2))) := by
    simpa only [Pi.mul_apply] using
      tendsto_const_nhds.mul
        ((hU.norm.pow 2).sub tendsto_const_nhds)
  have h4 :
      Tendsto
        (fun t : ℝ => (sigma T t ^ 2 / 8) * ‖P.V t‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hraw := ((hs.pow 2).div_const 8).mul (hV.norm.pow 2)
    norm_num at hraw
    exact hraw
  have h5 :
      Tendsto
        (fun t : ℝ =>
          (varpiT T * sigma T t * rho T t / 2) *
            ⟪P.X t - xStar, P.V t⟫_ℝ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hv :
        Tendsto (fun _t : ℝ => varpiT T)
          (𝓝[>] (0 : ℝ)) (𝓝 (varpiT T)) :=
      tendsto_const_nhds
    have hc :=
      (((hv.mul hs).mul hr).div_const 2)
    have hraw := hc.mul hinnerU
    norm_num at hraw
    exact hraw
  have h6 :
      Tendsto
        (fun t : ℝ =>
          (varpiT T * sigma T t ^ 3 / 4) *
            ⟪P.X t - P.X T, P.V t⟫_ℝ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hv :
        Tendsto (fun _t : ℝ => varpiT T)
          (𝓝[>] (0 : ℝ)) (𝓝 (varpiT T)) :=
      tendsto_const_nhds
    have hc :=
      ((hv.mul (hs.pow 3)).div_const 4)
    have hraw := hc.mul hinnerT
    norm_num at hraw
    exact hraw
  have hexpanded0 :=
    (((((h1.add h2).add h3).add h4).add h5).add h6)
  have hexpanded :
      Tendsto
        (fun t : ℝ =>
          (1 - rho T t) * (M.f (P.X t) - M.f xStar)
            + terminalFunctionCoeff T t *
              (M.f (P.X t) - M.f (P.X T))
            + (varpiT T ^ 2 / 2) *
              (‖P.X t - xStar‖ ^ 2 - ‖P.X T - xStar‖ ^ 2)
            + (sigma T t ^ 2 / 8) * ‖P.V t‖ ^ 2
            + (varpiT T * sigma T t * rho T t / 2) *
              ⟪P.X t - xStar, P.V t⟫_ℝ
            + (varpiT T * sigma T t ^ 3 / 4) *
              ⟪P.X t - P.X T, P.V t⟫_ℝ)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((varpiT T ^ 2 / 2) *
          (‖x0 - xStar‖ ^ 2 - ‖P.X T - xStar‖ ^ 2))) := by
    simpa only [zero_add, add_zero] using hexpanded0
  have hexpanded' :
      Tendsto (expandedLyapunov M T xStar x0 P)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((varpiT T ^ 2 / 2) *
          (‖x0 - xStar‖ ^ 2 - ‖P.X T - xStar‖ ^ 2))) := by
    apply hexpanded.congr'
    exact Filter.Eventually.of_forall fun t => by
      rfl
  apply hexpanded'.congr'
  have hlt :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < T := by
    have hlt' : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < T :=
      Iio_mem_nhds hT
    exact hlt'.filter_mono inf_le_left
  filter_upwards [eventually_mem_nhdsWithin, hlt] with t ht0 htT
  exact (lyapunov_eq_expanded xStar P hT ⟨ht0, htT⟩).symm

private theorem terminal_sub_tendsto_nhdsLT
    {T : ℝ} :
    Tendsto (fun delta : ℝ => T - delta)
      (𝓝[>] (0 : ℝ)) (𝓝[<] T) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hdelta :
        Tendsto (fun delta : ℝ => delta)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left inf_le_left
    simpa using
      (tendsto_const_nhds.sub hdelta :
        Tendsto (fun delta : ℝ => T - delta)
          (𝓝[>] (0 : ℝ)) (𝓝 (T - 0)))
  · filter_upwards [eventually_mem_nhdsWithin] with delta hdelta
    exact sub_lt_self T hdelta

private theorem terminal_delta_tendsto_to_left
    {T a : ℝ} {f : ℝ → ℝ}
    (h :
      Tendsto (fun delta : ℝ => f (T - delta))
        (𝓝[>] (0 : ℝ)) (𝓝 a)) :
    Tendsto f (𝓝[<] T) (𝓝 a) := by
  have hid : Tendsto (fun t : ℝ => t)
      (𝓝[<] T) (𝓝 T) :=
    tendsto_id.mono_left inf_le_left
  have hzero :
      Tendsto (fun t : ℝ => T - t)
        (𝓝[<] T) (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_const_nhds.sub hid :
        Tendsto (fun t : ℝ => T - t)
          (𝓝[<] T) (𝓝 (T - T)))
  have hsub :
      Tendsto (fun t : ℝ => T - t)
        (𝓝[<] T) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hzero, ?_⟩
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact sub_pos.mpr (show t < T from ht)
  have hcomp := h.comp hsub
  change
    Tendsto (fun t : ℝ => f (T - (T - t)))
      (𝓝[<] T) (𝓝 a) at hcomp
  simpa only [Function.comp_apply, sub_sub_cancel] using hcomp

private theorem trajectory_terminal_position_tendsto
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    Tendsto (fun delta : ℝ => P.X (T - delta))
      (𝓝[>] (0 : ℝ)) (𝓝 (P.X T)) := by
  have hcont :=
    (P.X_continuous T ⟨hT.le, le_rfl⟩).mono
      Ioo_subset_Icc_self
  have hleft :
      Tendsto P.X (𝓝[<] T) (𝓝 (P.X T)) := by
    simpa only [ContinuousWithinAt,
      nhdsWithin_Ioo_eq_nhdsLT hT] using hcont
  exact hleft.comp terminal_sub_tendsto_nhdsLT

private theorem trajectory_terminal_velocity_tendsto
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    Tendsto (fun delta : ℝ => P.V (T - delta))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : E)) := by
  have hcont :=
    (P.V_continuous T ⟨hT.le, le_rfl⟩).mono
      Ioo_subset_Icc_self
  have hleft :
      Tendsto P.V (𝓝[<] T) (𝓝 (P.V T)) := by
    simpa only [ContinuousWithinAt,
      nhdsWithin_Ioo_eq_nhdsLT hT] using hcont
  have h := hleft.comp terminal_sub_tendsto_nhdsLT
  change
    Tendsto (fun delta : ℝ => P.V (T - delta))
      (𝓝[>] (0 : ℝ)) (𝓝 (P.V T)) at h
  rw [P.velocity_horizon_eq_zero hT] at h
  exact h

/-- The rigorously derived terminal endpoint limit of the Lyapunov
function. -/
theorem lyapunov_terminal_limit
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    Tendsto (lyapunov M T xStar x0 P)
      (𝓝[<] T)
      (𝓝 (M.f (P.X T) - M.f xStar +
        ‖M.grad (P.X T)‖ ^ 2 / (2 * varpiT T ^ 2))) := by
  let v : ℝ := varpiT T
  let g : E := M.grad (P.X T)
  let r : ℝ → ℝ := fun delta => rho T (T - delta)
  let s : ℝ → ℝ := fun delta => sigma T (T - delta)
  let Xd : ℝ → E := fun delta => P.X (T - delta)
  let Vd : ℝ → E := fun delta => P.V (T - delta)
  have hv : 0 < v := by
    simpa [v] using varpiT_pos hT
  have hdelta :
      Tendsto (fun delta : ℝ => delta)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left inf_le_left
  have hr0 :
      Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [r] using rho_terminal_tendsto_zero hT
  have hrn :
      Tendsto (fun delta : ℝ => r delta / delta ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (v ^ 2 / 4)) := by
    simpa [r, v] using rho_terminal_normalized_tendsto hT
  have hsn :
      Tendsto (fun delta : ℝ => delta * s delta)
        (𝓝[>] (0 : ℝ)) (𝓝 (2 / v)) := by
    simpa [s, v] using sigma_terminal_normalized_tendsto hT
  have hX :
      Tendsto Xd (𝓝[>] (0 : ℝ)) (𝓝 (P.X T)) := by
    simpa [Xd] using trajectory_terminal_position_tendsto P hT
  have hV :
      Tendsto Vd (𝓝[>] (0 : ℝ)) (𝓝 (0 : E)) := by
    simpa [Vd] using trajectory_terminal_velocity_tendsto P hT
  have hfX :
      Tendsto (fun delta : ℝ => M.f (Xd delta))
        (𝓝[>] (0 : ℝ)) (𝓝 (M.f (P.X T))) :=
    (M.hasGradient (P.X T)).continuousAt.tendsto.comp hX
  have hVn :
      Tendsto (fun delta : ℝ => delta⁻¹ • Vd delta)
        (𝓝[>] (0 : ℝ)) (𝓝 (-g)) := by
    simpa [Vd, g] using P.velocity_terminal_normalized_tendsto hT
  have hXn :
      Tendsto
        (fun delta : ℝ =>
          (delta ^ 2)⁻¹ • (Xd delta - P.X T))
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2 : ℝ) • g)) := by
    simpa [Xd, g] using P.position_terminal_normalized_tendsto hT
  have hfn :
      Tendsto
        (fun delta : ℝ =>
          (M.f (Xd delta) - M.f (P.X T)) / delta ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (‖g‖ ^ 2 / 2)) := by
    simpa [Xd, g] using P.objective_terminal_normalized_tendsto hT
  have h1 :
      Tendsto
        (fun delta : ℝ =>
          (1 - r delta) * (M.f (Xd delta) - M.f xStar))
        (𝓝[>] (0 : ℝ))
        (𝓝 (M.f (P.X T) - M.f xStar)) := by
    have hone :
        Tendsto (fun _delta : ℝ => (1 : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have hfstar :
        Tendsto (fun _delta : ℝ => M.f xStar)
          (𝓝[>] (0 : ℝ)) (𝓝 (M.f xStar)) :=
      tendsto_const_nhds
    have hraw := (hone.sub hr0).mul (hfX.sub hfstar)
    norm_num at hraw
    exact hraw
  have h2 :
      Tendsto
        (fun delta : ℝ =>
          terminalFunctionCoeff T (T - delta) *
            (M.f (Xd delta) - M.f (P.X T)))
        (𝓝[>] (0 : ℝ)) (𝓝 (‖g‖ ^ 2 / v ^ 2)) := by
    have hnum :
        Tendsto (fun delta : ℝ => (1 - r delta) ^ 2 / 2)
          (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
      have hone :
          Tendsto (fun _delta : ℝ => (1 : ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
        tendsto_const_nhds
      have hraw := ((hone.sub hr0).pow 2).div_const 2
      norm_num at hraw
      exact hraw
    have hmodel :=
      (hnum.mul hfn).div hrn
        (by positivity : v ^ 2 / 4 ≠ 0)
    have hlimit :
        (1 / 2 : ℝ) * (‖g‖ ^ 2 / 2) / (v ^ 2 / 4) =
          ‖g‖ ^ 2 / v ^ 2 := by
      field_simp [hv.ne']
      ring
    rw [hlimit] at hmodel
    apply hmodel.congr'
    have hlt :
        ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), delta < T := by
      have hlt' : ∀ᶠ delta : ℝ in 𝓝 (0 : ℝ), delta < T :=
        Iio_mem_nhds hT
      exact hlt'.filter_mono inf_le_left
    filter_upwards [eventually_mem_nhdsWithin, hlt] with delta hd hdeltaT
    have hdpos : 0 < delta := hd
    have hd0 : delta ≠ 0 := hdpos.ne'
    have ht : T - delta ∈ Ioo (0 : ℝ) T := by
      constructor <;> linarith [hdpos]
    have hrne : r delta ≠ 0 := by
      simpa [r] using (rho_pos_lt_one hT ht).1.ne'
    unfold terminalFunctionCoeff
    dsimp [r, Xd]
    field_simp [hd0, hrne]
  have h3 :
      Tendsto
        (fun delta : ℝ =>
          (v ^ 2 / 2) *
            (‖Xd delta - xStar‖ ^ 2 -
              ‖P.X T - xStar‖ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hU := hX.sub
      (tendsto_const_nhds :
        Tendsto (fun _delta : ℝ => xStar)
          (𝓝[>] (0 : ℝ)) (𝓝 xStar))
    have hconstNorm :
        Tendsto
          (fun _delta : ℝ => ‖P.X T - xStar‖ ^ 2)
          (𝓝[>] (0 : ℝ))
          (𝓝 (‖P.X T - xStar‖ ^ 2)) :=
      tendsto_const_nhds
    have hvcoef :
        Tendsto (fun _delta : ℝ => v ^ 2 / 2)
          (𝓝[>] (0 : ℝ)) (𝓝 (v ^ 2 / 2)) :=
      tendsto_const_nhds
    have hraw :=
      hvcoef.mul ((hU.norm.pow 2).sub hconstNorm)
    norm_num at hraw
    exact hraw
  have h4 :
      Tendsto
        (fun delta : ℝ =>
          (s delta ^ 2 / 8) * ‖Vd delta‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (‖g‖ ^ 2 / (2 * v ^ 2))) := by
    have hproduct := hsn.smul hVn
    have hnormed := (hproduct.norm.pow 2).div_const 8
    have hlimit :
        ‖(2 / v) • (-g)‖ ^ 2 / 8 =
          ‖g‖ ^ 2 / (2 * v ^ 2) := by
      rw [norm_smul, norm_neg, Real.norm_eq_abs,
        abs_of_pos (div_pos (by norm_num) hv)]
      field_simp [hv.ne']
      ring
    rw [hlimit] at hnormed
    apply hnormed.congr'
    have hlt :
        ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), delta < T := by
      have hlt' : ∀ᶠ delta : ℝ in 𝓝 (0 : ℝ), delta < T :=
        Iio_mem_nhds hT
      exact hlt'.filter_mono inf_le_left
    filter_upwards [eventually_mem_nhdsWithin, hlt] with delta hd hdeltaT
    have hdpos : 0 < delta := hd
    have hd0 : delta ≠ 0 := hdpos.ne'
    have ht : T - delta ∈ Ioo (0 : ℝ) T := by
      constructor <;> linarith [hdpos]
    have hspos : 0 < s delta := by
      simpa [s] using sigma_pos hT ht
    have hvec :
        (delta * s delta) • (delta⁻¹ • Vd delta) =
          s delta • Vd delta := by
      rw [smul_smul]
      congr 1
      field_simp [hd0]
    rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    ring
  have hrOverDelta :
      Tendsto (fun delta : ℝ => r delta / delta)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hmodel := hrn.mul hdelta
    norm_num at hmodel
    apply hmodel.congr'
    filter_upwards [eventually_mem_nhdsWithin] with delta hd
    have hdpos : 0 < delta := hd
    field_simp [hdpos.ne']
  have hsr :
      Tendsto (fun delta : ℝ => s delta * r delta)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hmodel := hsn.mul hrOverDelta
    norm_num at hmodel
    apply hmodel.congr'
    filter_upwards [eventually_mem_nhdsWithin] with delta hd
    have hdpos : 0 < delta := hd
    have hd0 : delta ≠ 0 := hdpos.ne'
    rw [div_eq_mul_inv]
    calc
      delta * s delta * (r delta * delta⁻¹) =
          (delta * delta⁻¹) * (s delta * r delta) := by ring
      _ = s delta * r delta := by rw [mul_inv_cancel₀ hd0, one_mul]
  have h5 :
      Tendsto
        (fun delta : ℝ =>
          (v * s delta * r delta / 2) *
            ⟪Xd delta - xStar, Vd delta⟫_ℝ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hxstar :
        Tendsto (fun _delta : ℝ => xStar)
          (𝓝[>] (0 : ℝ)) (𝓝 xStar) :=
      tendsto_const_nhds
    have hinner :=
      Filter.Tendsto.inner (𝕜 := ℝ)
        (hX.sub hxstar) hV
    have hvconst :
        Tendsto (fun _delta : ℝ => v)
          (𝓝[>] (0 : ℝ)) (𝓝 v) :=
      tendsto_const_nhds
    have hc := (hvconst.mul hsr).div_const 2
    have hraw := hc.mul hinner
    norm_num at hraw
    apply hraw.congr'
    exact Filter.Eventually.of_forall fun delta => by ring
  have h6 :
      Tendsto
        (fun delta : ℝ =>
          (v * s delta ^ 3 / 4) *
            ⟪Xd delta - P.X T, Vd delta⟫_ℝ)
        (𝓝[>] (0 : ℝ)) (𝓝 (-‖g‖ ^ 2 / v ^ 2)) := by
    have hinner :=
      Filter.Tendsto.inner (𝕜 := ℝ) hXn hVn
    have hinner' :
        Tendsto
          (fun delta : ℝ =>
            ⟪(delta ^ 2)⁻¹ • (Xd delta - P.X T),
              delta⁻¹ • Vd delta⟫_ℝ)
          (𝓝[>] (0 : ℝ)) (𝓝 (-‖g‖ ^ 2 / 2)) := by
      have hlimit :
          ⟪(1 / 2 : ℝ) • g, -g⟫_ℝ =
            -‖g‖ ^ 2 / 2 := by
        rw [real_inner_smul_left, inner_neg_right,
          real_inner_self_eq_norm_sq]
        ring
      rw [hlimit] at hinner
      exact hinner
    have hvconst :
        Tendsto (fun _delta : ℝ => v)
          (𝓝[>] (0 : ℝ)) (𝓝 v) :=
      tendsto_const_nhds
    have hc := (hvconst.mul (hsn.pow 3)).div_const 4
    have hmodel := hc.mul hinner'
    have hlimit :
        (v * (2 / v) ^ 3 / 4) *
            (-‖g‖ ^ 2 / 2) =
          -‖g‖ ^ 2 / v ^ 2 := by
      field_simp [hv.ne']
      ring
    rw [hlimit] at hmodel
    apply hmodel.congr'
    filter_upwards [eventually_mem_nhdsWithin] with delta hd
    have hdpos : 0 < delta := hd
    have hd0 : delta ≠ 0 := hdpos.ne'
    simp only [real_inner_smul_left, real_inner_smul_right]
    field_simp [hd0]
  have hsum0 :=
    (((((h1.add h2).add h3).add h4).add h5).add h6)
  have hsum :
      Tendsto
        (fun delta : ℝ =>
          (1 - r delta) * (M.f (Xd delta) - M.f xStar)
            + terminalFunctionCoeff T (T - delta) *
              (M.f (Xd delta) - M.f (P.X T))
            + (v ^ 2 / 2) *
              (‖Xd delta - xStar‖ ^ 2 -
                ‖P.X T - xStar‖ ^ 2)
            + (s delta ^ 2 / 8) * ‖Vd delta‖ ^ 2
            + (v * s delta * r delta / 2) *
              ⟪Xd delta - xStar, Vd delta⟫_ℝ
            + (v * s delta ^ 3 / 4) *
              ⟪Xd delta - P.X T, Vd delta⟫_ℝ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (M.f (P.X T) - M.f xStar +
          ‖g‖ ^ 2 / (2 * v ^ 2))) := by
    convert hsum0 using 1
    ring_nf
  have hexpanded :
      Tendsto
        (fun delta : ℝ =>
          expandedLyapunov M T xStar x0 P (T - delta))
        (𝓝[>] (0 : ℝ))
        (𝓝 (M.f (P.X T) - M.f xStar +
          ‖g‖ ^ 2 / (2 * v ^ 2))) := by
    apply hsum.congr'
    exact Filter.Eventually.of_forall fun delta => by
      rfl
  have hlyapunov :
      Tendsto
        (fun delta : ℝ =>
          lyapunov M T xStar x0 P (T - delta))
        (𝓝[>] (0 : ℝ))
        (𝓝 (M.f (P.X T) - M.f xStar +
          ‖g‖ ^ 2 / (2 * v ^ 2))) := by
    apply hexpanded.congr'
    have hlt :
        ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), delta < T := by
      have hlt' : ∀ᶠ delta : ℝ in 𝓝 (0 : ℝ), delta < T :=
        Iio_mem_nhds hT
      exact hlt'.filter_mono inf_le_left
    filter_upwards [eventually_mem_nhdsWithin, hlt] with delta hd hdeltaT
    have hdpos : 0 < delta := hd
    have ht : T - delta ∈ Ioo (0 : ℝ) T := by
      constructor <;> linarith [hdpos]
    exact
      (lyapunov_eq_expanded xStar P hT ht).symm
  simpa [v, g] using terminal_delta_tendsto_to_left hlyapunov

/-- The terminal Lyapunov limit is bounded by its initial limit. -/
theorem terminal_energy_le_initial_energy
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    M.f (P.X T) - M.f xStar +
          ‖M.grad (P.X T)‖ ^ 2 / (2 * varpiT T ^ 2)
      ≤
      (varpiT T ^ 2 / 2) *
        (‖x0 - xStar‖ ^ 2 - ‖P.X T - xStar‖ ^ 2) := by
  let mid : ℝ := T / 2
  have hmid : mid ∈ Ioo (0 : ℝ) T := by
    dsimp [mid]
    constructor <;> linarith
  have hmono := lyapunov_antitoneOn xStar P hT
  have hmid_le_initial :
      lyapunov M T xStar x0 P mid ≤
        (varpiT T ^ 2 / 2) *
          (‖x0 - xStar‖ ^ 2 - ‖P.X T - xStar‖ ^ 2) := by
    apply ge_of_tendsto (lyapunov_initial_limit xStar P hT)
    have hlt :
        ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < mid := by
      have hlt' : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), s < mid :=
        Iio_mem_nhds hmid.1
      exact hlt'.filter_mono inf_le_left
    filter_upwards [eventually_mem_nhdsWithin, hlt] with s hs0 hsmid
    have hs : s ∈ Ioo (0 : ℝ) T :=
      ⟨hs0, hsmid.trans hmid.2⟩
    exact hmono hs hmid hsmid.le
  have hterminal_le_mid :
      M.f (P.X T) - M.f xStar +
          ‖M.grad (P.X T)‖ ^ 2 / (2 * varpiT T ^ 2)
        ≤ lyapunov M T xStar x0 P mid := by
    apply le_of_tendsto (lyapunov_terminal_limit xStar P hT)
    have hgt :
        ∀ᶠ t : ℝ in 𝓝[<] T, mid < t := by
      have hgt' : ∀ᶠ t : ℝ in 𝓝 T, mid < t :=
        Ioi_mem_nhds hmid.2
      exact hgt'.filter_mono inf_le_left
    filter_upwards [eventually_mem_nhdsWithin, hgt] with t htT hmidt
    have ht : t ∈ Ioo (0 : ℝ) T :=
      ⟨hmid.1.trans hmidt, htT⟩
    exact hmono hmid ht hmidt.le
  exact hterminal_le_mid.trans hmid_le_initial

/-- The stronger combined endpoint inequality appearing at the end of the
continuous-time appendix proof. -/
theorem combined_endpoint_inequality
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    ‖M.grad (P.X T)‖ ^ 2
        + 2 * varpiT T ^ 2 *
          (M.f (P.X T) - M.f xStar)
        + varpiT T ^ 4 * ‖P.X T - xStar‖ ^ 2
      ≤
      varpiT T ^ 4 * ‖x0 - xStar‖ ^ 2 := by
  let v : ℝ := varpiT T
  have hv : 0 < v := by
    simpa [v] using varpiT_pos hT
  have henergy := terminal_energy_le_initial_energy xStar P hT
  have hscaled :=
    mul_le_mul_of_nonneg_left henergy
      (show 0 ≤ 2 * v ^ 2 by positivity)
  calc
    ‖M.grad (P.X T)‖ ^ 2
          + 2 * v ^ 2 * (M.f (P.X T) - M.f xStar)
          + v ^ 4 * ‖P.X T - xStar‖ ^ 2 =
        (2 * v ^ 2) *
            (M.f (P.X T) - M.f xStar +
              ‖M.grad (P.X T)‖ ^ 2 / (2 * v ^ 2))
          + v ^ 4 * ‖P.X T - xStar‖ ^ 2 := by
            field_simp [hv.ne']
            ring
    _ ≤
        (2 * v ^ 2) *
            ((v ^ 2 / 2) *
              (‖x0 - xStar‖ ^ 2 -
                ‖P.X T - xStar‖ ^ 2))
          + v ^ 4 * ‖P.X T - xStar‖ ^ 2 := by
            simpa [v] using
              add_le_add_right hscaled
                (v ^ 4 * ‖P.X T - xStar‖ ^ 2)
    _ = v ^ 4 * ‖x0 - xStar‖ ^ 2 := by ring

end Continuous

/-- Both manuscript endpoint bounds for a closed-interval continuous
LemniAcc trajectory. -/
theorem continuousTime_lyapunov
    (M : SmoothConvexModel E) (T : ℝ) (hT : 0 < T)
    (xStar : E) (hxStar : M.IsMinimizer xStar)
    (x0 : E) (P : ContinuousTrajectory M T x0) :
    ‖M.grad (P.X T)‖ ^ 2 ≤
        (Lemniscatic.varpi ^ 4 / T ^ 4) *
          ‖x0 - xStar‖ ^ 2
      ∧
      M.f (P.X T) - M.f xStar ≤
        (Lemniscatic.varpi ^ 2 / (2 * T ^ 2)) *
          ‖x0 - xStar‖ ^ 2 := by
  let v : ℝ := Lemniscatic.varpiT T
  have hv : 0 < v := by
    simpa [v] using Lemniscatic.varpiT_pos hT
  have hstrong :=
    Continuous.combined_endpoint_inequality xStar P hT
  have hstrong' :
      ‖M.grad (P.X T)‖ ^ 2
          + 2 * v ^ 2 * (M.f (P.X T) - M.f xStar)
          + v ^ 4 * ‖P.X T - xStar‖ ^ 2
        ≤ v ^ 4 * ‖x0 - xStar‖ ^ 2 := by
    simpa [v] using hstrong
  have hgap :
      0 ≤ M.f (P.X T) - M.f xStar := by
    exact sub_nonneg.mpr (hxStar (P.X T))
  have hterminal :
      0 ≤ v ^ 4 * ‖P.X T - xStar‖ ^ 2 := by positivity
  have hgrad :
      ‖M.grad (P.X T)‖ ^ 2 ≤
        v ^ 4 * ‖x0 - xStar‖ ^ 2 := by
    have hgapTerm :
        0 ≤ 2 * v ^ 2 * (M.f (P.X T) - M.f xStar) := by
      positivity
    nlinarith [hstrong']
  have hfunction :
      M.f (P.X T) - M.f xStar ≤
        (v ^ 2 / 2) * ‖x0 - xStar‖ ^ 2 := by
    have hgradNonneg :
        0 ≤ ‖M.grad (P.X T)‖ ^ 2 := sq_nonneg _
    have hscaled :
        2 * v ^ 2 * (M.f (P.X T) - M.f xStar) ≤
          v ^ 4 * ‖x0 - xStar‖ ^ 2 := by
      nlinarith [hstrong']
    have hscaled' :
        (M.f (P.X T) - M.f xStar) * (2 * v ^ 2) ≤
          v ^ 4 * ‖x0 - xStar‖ ^ 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
    have hdiv :=
      (le_div_iff₀ (show 0 < 2 * v ^ 2 by positivity)).2 hscaled'
    calc
      M.f (P.X T) - M.f xStar ≤
          v ^ 4 * ‖x0 - xStar‖ ^ 2 /
            (2 * v ^ 2) := hdiv
      _ = (v ^ 2 / 2) * ‖x0 - xStar‖ ^ 2 := by
            field_simp [hv.ne']
  have hv4 :
      v ^ 4 = Lemniscatic.varpi ^ 4 / T ^ 4 := by
    dsimp [v, Lemniscatic.varpiT]
    field_simp [hT.ne']
  have hv2 :
      v ^ 2 / 2 =
        Lemniscatic.varpi ^ 2 / (2 * T ^ 2) := by
    dsimp [v, Lemniscatic.varpiT]
    field_simp [hT.ne']
  rw [hv4] at hgrad
  rw [hv2] at hfunction
  exact ⟨hgrad, hfunction⟩

end LemniAcc
