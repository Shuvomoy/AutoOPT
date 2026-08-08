import LemniAcc.Model
import LemniAcc.Continuous.Coefficients
import Mathlib.Analysis.Calculus.FDeriv.Extend

open scoped InnerProductSpace Topology
open Set Filter

set_option autoImplicit false

namespace LemniAcc

open Lemniscatic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The exact trajectory interface used by the continuous-time theorem.

The terminal identities are deliberately absent: they are consequences of
the singular ODE, continuity, and the interior derivative identities. -/
structure ContinuousTrajectory
    (M : SmoothConvexModel E) (T : ℝ) (x0 : E) where
  X : ℝ → E
  V : ℝ → E
  A : ℝ → E
  X_continuous : ContinuousOn X (Icc (0 : ℝ) T)
  V_continuous : ContinuousOn V (Icc (0 : ℝ) T)
  A_continuous : ContinuousOn A (Icc (0 : ℝ) T)
  X_derivative :
    ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt X (V t) t
  V_derivative :
    ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V (A t) t
  ode :
    ∀ t ∈ Ioo (0 : ℝ) T,
      A t + gamma T t • V t + 2 • M.grad (X t) = 0
  X_zero : X 0 = x0
  V_zero : V 0 = 0

theorem terminalDeltaLimit_to_leftLimit
    {T : ℝ} {c : ℝ → ℝ}
    (hc :
      Tendsto (fun delta : ℝ => delta * c (T - delta))
        (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℝ))) :
    Tendsto (fun t : ℝ => (T - t) * c t)
      (𝓝[<] T) (𝓝 (3 : ℝ)) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
    tendsto_id.mono_left inf_le_left
  have hzero : Tendsto (fun t : ℝ => T - t)
      (𝓝[<] T) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hid :
      Tendsto (fun t : ℝ => T - t)
        (𝓝[<] T) (𝓝 (T - T)))
  have hsub :
      Tendsto (fun t : ℝ => T - t)
        (𝓝[<] T) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hzero, ?_⟩
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact sub_pos.mpr (show t < T from ht)
  have hcomp := hc.comp hsub
  change Tendsto
    (fun t : ℝ => (T - t) * c (T - (T - t)))
    (𝓝[<] T) (𝓝 (3 : ℝ)) at hcomp
  simpa only [sub_sub_cancel] using hcomp

omit [CompleteSpace E] in
private theorem endpointVelocityZero
    {T : ℝ} (hT : 0 < T)
    {V A G : ℝ → E} {c : ℝ → ℝ}
    (hV : ContinuousOn V (Icc (0 : ℝ) T))
    (hA : ContinuousOn A (Icc (0 : ℝ) T))
    (hG : ContinuousOn G (Icc (0 : ℝ) T))
    (hc : Tendsto (fun t : ℝ => (T - t) * c t)
      (𝓝[<] T) (𝓝 (3 : ℝ)))
    (hODE : ∀ t ∈ Ioo (0 : ℝ) T,
      A t + c t • V t + 2 • G t = 0) :
    V T = 0 := by
  have hVlim : Tendsto V (𝓝[<] T) (𝓝 (V T)) := by
    have hcont :=
      (hV T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hT]
      using hcont
  have hAlim : Tendsto A (𝓝[<] T) (𝓝 (A T)) := by
    have hcont :=
      (hA T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hT]
      using hcont
  have hGlim : Tendsto G (𝓝[<] T) (𝓝 (G T)) := by
    have hcont :=
      (hG T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hT]
      using hcont
  have hzero : Tendsto (fun t : ℝ => T - t)
      (𝓝[<] T) (𝓝 (0 : ℝ)) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
      tendsto_id.mono_left inf_le_left
    simpa using (tendsto_const_nhds.sub hid :
      Tendsto (fun t : ℝ => T - t)
        (𝓝[<] T) (𝓝 (T - T)))
  have hscaled :
      Tendsto
        (fun t : ℝ =>
          (T - t) • A t + ((T - t) * c t) • V t +
            (T - t) • (2 • G t))
        (𝓝[<] T) (𝓝 ((3 : ℝ) • V T)) := by
    simpa using
      ((hzero.smul hAlim).add (hc.smul hVlim) |>.add
        (hzero.smul (tendsto_const_nhds.smul hGlim)))
  have heq :
      (fun t : ℝ =>
        (T - t) • A t + ((T - t) * c t) • V t +
          (T - t) • (2 • G t)) =ᶠ[𝓝[<] T]
        fun _ => (0 : E) := by
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    have h :=
      congrArg (fun z : E => (T - t) • z) (hODE t ht)
    simpa only [smul_add, mul_smul, zero_smul, smul_zero]
      using h
  have hzeroLimit :
      Tendsto
        (fun t : ℝ =>
          (T - t) • A t + ((T - t) * c t) • V t +
            (T - t) • (2 • G t))
        (𝓝[<] T) (𝓝 (0 : E)) :=
    tendsto_const_nhds.congr' heq.symm
  have hthree : (3 : ℝ) • V T = 0 :=
    tendsto_nhds_unique hscaled hzeroLimit
  exact
    (smul_eq_zero_iff_right
      (by norm_num : (3 : ℝ) ≠ 0)).mp hthree

omit [CompleteSpace E] in
private theorem endpointAccelerationEq
    {T : ℝ} (hT : 0 < T)
    {V A G : ℝ → E} {c : ℝ → ℝ}
    (hV : ContinuousOn V (Icc (0 : ℝ) T))
    (hA : ContinuousOn A (Icc (0 : ℝ) T))
    (hG : ContinuousOn G (Icc (0 : ℝ) T))
    (hVA : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt V (A t) t)
    (hc : Tendsto (fun t : ℝ => (T - t) * c t)
      (𝓝[<] T) (𝓝 (3 : ℝ)))
    (hODE : ∀ t ∈ Ioo (0 : ℝ) T,
      A t + c t • V t + 2 • G t = 0) :
    A T = G T := by
  have hVT : V T = 0 :=
    endpointVelocityZero hT hV hA hG hc hODE
  have hVcont : ContinuousWithinAt V (Ioo (0 : ℝ) T) T :=
    (hV T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self
  have hAleft : Tendsto A (𝓝[<] T) (𝓝 (A T)) := by
    have hcont :=
      (hA T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hT]
      using hcont
  have hderivA :
      Tendsto (fun t : ℝ => deriv V t)
        (𝓝[<] T) (𝓝 (A T)) := by
    apply hAleft.congr'
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    exact (hVA t ht).deriv.symm
  have hVdiff : DifferentiableOn ℝ V (Ioo (0 : ℝ) T) :=
    fun t ht =>
      (hVA t ht).differentiableAt.differentiableWithinAt
  have hVAT :
      HasDerivWithinAt V (A T) (Iic T) T :=
    hasDerivWithinAt_Iic_of_tendsto_deriv
      hVdiff hVcont (Ioo_mem_nhdsLT hT) hderivA
  have hslope :
      Tendsto (slope V T) (𝓝[<] T) (𝓝 (A T)) := by
    have hs := hasDerivWithinAt_iff_tendsto_slope.mp hVAT
    simpa only [Iic_sdiff_right] using hs
  have hAlim : Tendsto A (𝓝[<] T) (𝓝 (A T)) := hAleft
  have hGlim : Tendsto G (𝓝[<] T) (𝓝 (G T)) := by
    have hcont :=
      (hG T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hT]
      using hcont
  have hcoef :
      Tendsto (fun t : ℝ => (t - T) * c t)
        (𝓝[<] T) (𝓝 (-3 : ℝ)) := by
    have heq :
        (fun t : ℝ => (t - T) * c t) =
          fun t : ℝ => -((T - t) * c t) := by
      funext t
      ring
    rw [heq]
    exact hc.neg
  have hcV :
      Tendsto (fun t : ℝ => c t • V t)
        (𝓝[<] T) (𝓝 ((-3 : ℝ) • A T)) := by
    have hprod := hcoef.smul hslope
    apply hprod.congr'
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    simp only [slope, vsub_eq_sub, hVT, sub_zero, smul_smul]
    have hne : t - T ≠ 0 := sub_ne_zero.mpr ht.2.ne
    have hscalar : (t - T) * c t * (t - T)⁻¹ = c t := by
      field_simp
    rw [hscalar]
  have hleft :
      Tendsto (fun t : ℝ => A t + c t • V t + 2 • G t)
        (𝓝[<] T)
        (𝓝 (A T + (-3 : ℝ) • A T + 2 • G T)) :=
    hAlim.add hcV |>.add
      (tendsto_const_nhds.smul hGlim)
  have heq :
      (fun t : ℝ => A t + c t • V t + 2 • G t)
        =ᶠ[𝓝[<] T] fun _ => (0 : E) := by
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    exact hODE t ht
  have hzeroLimit :
      Tendsto (fun t : ℝ => A t + c t • V t + 2 • G t)
        (𝓝[<] T) (𝓝 (0 : E)) :=
    tendsto_const_nhds.congr' heq.symm
  have hlimit :
      A T + (-3 : ℝ) • A T + 2 • G T = 0 :=
    tendsto_nhds_unique hleft hzeroLimit
  have htwo : (2 : ℝ) • (G T - A T) = 0 := by
    calc
      (2 : ℝ) • (G T - A T) =
          A T + (-3 : ℝ) • A T + 2 • G T := by module
      _ = 0 := hlimit
  have hGA : G T - A T = 0 :=
    (smul_eq_zero_iff_right
      (by norm_num : (2 : ℝ) ≠ 0)).mp htwo
  exact (sub_eq_zero.mp hGA).symm

omit [CompleteSpace E] in
private theorem endpointTaylor
    {T : ℝ} (hT : 0 < T)
    {X V A : ℝ → E}
    (hX : ContinuousOn X (Icc (0 : ℝ) T))
    (hV : ContinuousOn V (Icc (0 : ℝ) T))
    (hA : ContinuousOn A (Icc (0 : ℝ) T))
    (hXV : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt X (V t) t)
    (hVA : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt V (A t) t)
    (hVT : V T = 0) :
    ((fun delta : ℝ => V (T - delta) + delta • A T)
        =o[𝓝[>] (0 : ℝ)] fun delta : ℝ => delta) ∧
      ((fun delta : ℝ =>
          X (T - delta) - X T - (delta ^ 2 / 2) • A T)
        =o[𝓝[>] (0 : ℝ)] fun delta : ℝ => delta ^ 2) := by
  have hVcont : ContinuousWithinAt V (Ioo (0 : ℝ) T) T :=
    (hV T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self
  have hAleft : Tendsto A (𝓝[<] T) (𝓝 (A T)) := by
    have hcont :=
      (hA T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hT]
      using hcont
  have hderivA :
      Tendsto (fun t : ℝ => deriv V t)
        (𝓝[<] T) (𝓝 (A T)) := by
    apply hAleft.congr'
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    exact (hVA t ht).deriv.symm
  have hVdiff : DifferentiableOn ℝ V (Ioo (0 : ℝ) T) :=
    fun t ht =>
      (hVA t ht).differentiableAt.differentiableWithinAt
  have hVAT :
      HasDerivWithinAt V (A T) (Iic T) T :=
    hasDerivWithinAt_Iic_of_tendsto_deriv
      hVdiff hVcont (Ioo_mem_nhdsLT hT) hderivA
  have hXcont : ContinuousWithinAt X (Ioo (0 : ℝ) T) T :=
    (hX T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self
  have hVleft : Tendsto V (𝓝[<] T) (𝓝 (V T)) := by
    have hcont :=
      (hV T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hT]
      using hcont
  have hderivV :
      Tendsto (fun t : ℝ => deriv X t)
        (𝓝[<] T) (𝓝 (V T)) := by
    apply hVleft.congr'
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    exact (hXV t ht).deriv.symm
  have hXdiff : DifferentiableOn ℝ X (Ioo (0 : ℝ) T) :=
    fun t ht =>
      (hXV t ht).differentiableAt.differentiableWithinAt
  have hXVT :
      HasDerivWithinAt X (V T) (Iic T) T :=
    hasDerivWithinAt_Iic_of_tendsto_deriv
      hXdiff hXcont (Ioo_mem_nhdsLT hT) hderivV
  have hid : Tendsto (fun t : ℝ => t)
      (𝓝[<] T) (𝓝 T) :=
    tendsto_id.mono_left inf_le_left
  have hzero : Tendsto (fun t : ℝ => T - t)
      (𝓝[<] T) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hid :
      Tendsto (fun t : ℝ => T - t)
        (𝓝[<] T) (𝓝 (T - T)))
  have hback :
      Tendsto (fun delta : ℝ => T - delta)
        (𝓝[>] (0 : ℝ)) (𝓝[<] T) := by
    have hid0 :
        Tendsto (fun delta : ℝ => delta)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left inf_le_left
    have hlimit :
        Tendsto (fun delta : ℝ => T - delta)
          (𝓝[>] (0 : ℝ)) (𝓝 T) := by
      simpa using (tendsto_const_nhds.sub hid0 :
        Tendsto (fun delta : ℝ => T - delta)
          (𝓝[>] (0 : ℝ)) (𝓝 (T - 0)))
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hlimit, ?_⟩
    filter_upwards [eventually_mem_nhdsWithin] with delta hdelta
    exact sub_lt_self T (show 0 < delta from hdelta)
  constructor
  · have hrem := hVAT.isLittleO.mono
      (nhdsWithin_mono T Iio_subset_Iic_self)
    have hcomp := hrem.comp_tendsto hback
    change
      (fun delta : ℝ =>
        V (T - delta) - V T -
          ((T - delta) - T) • A T)
        =o[𝓝[>] (0 : ℝ)]
          fun delta : ℝ => (T - delta) - T at hcomp
    simpa [hVT] using hcomp.neg_right
  · let c : ℝ := T / 2
    let s : Set ℝ := Icc c T
    let RX : ℝ → E := fun t =>
      X t - X T - ((t - T) ^ 2 / 2) • A T
    let RV : ℝ → E := fun t =>
      V t - V T - (t - T) • A T
    have hcpos : 0 < c := by
      dsimp [c]
      linarith
    have hcT : c < T := by
      dsimp [c]
      linarith
    have hXs :
        ∀ t ∈ s, HasDerivWithinAt X (V t) s t := by
      intro t ht
      by_cases heq : t = T
      · subst t
        exact hXVT.mono (by
          intro u hu
          exact hu.2)
      · have htIoo : t ∈ Ioo (0 : ℝ) T := by
          constructor
          · exact hcpos.trans_le ht.1
          · exact lt_of_le_of_ne ht.2 heq
        exact (hXV t htIoo).hasDerivWithinAt
    have hRX :
        ∀ t ∈ s, HasDerivWithinAt RX (RV t) s t := by
      intro t ht
      have hquad :
          HasDerivAt
            (fun u : ℝ => ((u - T) ^ 2 / 2) • A T)
            ((t - T) • A T) t := by
        have hraw :=
          (((hasDerivAt_id t).sub_const T).pow 2).smul_const
            ((1 / 2 : ℝ) • A T)
        convert hraw using 1
        · funext u
          simp only [Pi.pow_apply, id_eq, smul_smul]
          congr 1
          ring
        · simp only [id_eq, smul_smul]
          congr 1
          ring
      change HasDerivWithinAt
        ((fun x : ℝ => X x - X T) -
          fun u : ℝ => ((u - T) ^ 2 / 2) • A T)
        (RV t) s t
      simpa [RV, hVT] using
        ((hXs t ht).sub_const (X T)).sub
          hquad.hasDerivWithinAt
    have hRV :
        RV =o[𝓝[s] T] fun t : ℝ => (t - T) ^ 1 := by
      have hrem := hVAT.isLittleO.mono
        (nhdsWithin_mono T (show s ⊆ Iic T by
          intro t ht
          exact ht.2))
      simpa only [RV, pow_one] using hrem
    have hRXO :
        (fun t : ℝ => RX t - RX T)
          =o[𝓝[s] T] fun t : ℝ => (t - T) ^ 2 :=
      Convex.isLittleO_pow_succ_real
        (convex_Icc c T) (right_mem_Icc.mpr hcT.le)
        hRX hRV
    have hmapS :
        Tendsto (fun delta : ℝ => T - delta)
          (𝓝[>] (0 : ℝ)) (𝓝[s] T) :=
      hback.mono_right
        (nhdsWithin_le_iff.mpr (Icc_mem_nhdsLT hcT))
    have hcomp := hRXO.comp_tendsto hmapS
    change
      (fun delta : ℝ => RX (T - delta) - RX T)
        =o[𝓝[>] (0 : ℝ)]
          fun delta : ℝ => ((T - delta) - T) ^ 2 at hcomp
    simpa [RX, hVT] using hcomp

omit [CompleteSpace E] in
private theorem quadraticLittleO_to_normalized
    {T : ℝ} {X : ℝ → E} {a : E}
    (h :
      (fun delta : ℝ =>
        X (T - delta) - X T - (delta ^ 2 / 2) • a)
        =o[𝓝[>] (0 : ℝ)] fun delta : ℝ => delta ^ 2) :
    Tendsto
      (fun delta : ℝ =>
        (delta ^ 2)⁻¹ • (X (T - delta) - X T))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2 : ℝ) • a)) := by
  have hrem := h.tendsto_inv_smul_nhds_zero
  have hmain :
      Tendsto
        (fun delta : ℝ =>
          (delta ^ 2)⁻¹ • ((delta ^ 2 / 2) • a))
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2 : ℝ) • a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mem_nhdsWithin] with delta hdelta
    rw [smul_smul]
    congr 1
    have hdelta0 : delta ≠ 0 :=
      ne_of_gt (show 0 < delta from hdelta)
    field_simp [pow_ne_zero 2 hdelta0]
  have hsum := hrem.add hmain
  have heq :
      (fun delta : ℝ =>
        (delta ^ 2)⁻¹ •
            (X (T - delta) - X T - (delta ^ 2 / 2) • a) +
          (delta ^ 2)⁻¹ • ((delta ^ 2 / 2) • a))
        =ᶠ[𝓝[>] (0 : ℝ)]
      fun delta : ℝ =>
        (delta ^ 2)⁻¹ • (X (T - delta) - X T) := by
    filter_upwards with delta
    rw [← smul_add]
    congr 1
    abel
  simpa only [zero_add] using hsum.congr' heq

namespace ContinuousTrajectory

variable {M : SmoothConvexModel E} {T : ℝ} {x0 : E}

theorem gradient_continuous
    (P : ContinuousTrajectory M T x0) :
    ContinuousOn (fun t : ℝ => M.grad (P.X t))
      (Icc (0 : ℝ) T) :=
  M.gradLipschitz.continuous.comp_continuousOn P.X_continuous

theorem gamma_left_limit
    (_P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    Tendsto (fun t : ℝ => (T - t) * gamma T t)
      (𝓝[<] T) (𝓝 (3 : ℝ)) :=
  terminalDeltaLimit_to_leftLimit
    (gamma_terminal_normalized_tendsto hT)

theorem velocity_hasDerivWithinAt_horizon
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    HasDerivWithinAt P.V (P.A T) (Iic T) T := by
  have hVcont :
      ContinuousWithinAt P.V (Ioo (0 : ℝ) T) T :=
    (P.V_continuous T ⟨hT.le, le_rfl⟩).mono
      Ioo_subset_Icc_self
  have hAleft :
      Tendsto P.A (𝓝[<] T) (𝓝 (P.A T)) := by
    have hcont :=
      (P.A_continuous T ⟨hT.le, le_rfl⟩).mono
        Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hT]
      using hcont
  have hderivA :
      Tendsto (fun t : ℝ => deriv P.V t)
        (𝓝[<] T) (𝓝 (P.A T)) := by
    apply hAleft.congr'
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    exact (P.V_derivative t ht).deriv.symm
  have hVdiff :
      DifferentiableOn ℝ P.V (Ioo (0 : ℝ) T) :=
    fun t ht =>
      (P.V_derivative t ht).differentiableAt.differentiableWithinAt
  exact hasDerivWithinAt_Iic_of_tendsto_deriv
    hVdiff hVcont (Ioo_mem_nhdsLT hT) hderivA

theorem velocity_horizon_eq_zero
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    P.V T = 0 :=
  endpointVelocityZero hT P.V_continuous P.A_continuous
    P.gradient_continuous (P.gamma_left_limit hT) P.ode

theorem acceleration_horizon_eq_gradient
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    P.A T = M.grad (P.X T) :=
  endpointAccelerationEq hT P.V_continuous P.A_continuous
    P.gradient_continuous P.V_derivative
    (P.gamma_left_limit hT) P.ode

theorem terminal_taylor_littleO
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    ((fun delta : ℝ =>
        P.V (T - delta) + delta • P.A T)
      =o[𝓝[>] (0 : ℝ)] fun delta : ℝ => delta) ∧
    ((fun delta : ℝ =>
        P.X (T - delta) - P.X T -
          (delta ^ 2 / 2) • P.A T)
      =o[𝓝[>] (0 : ℝ)] fun delta : ℝ => delta ^ 2) :=
  endpointTaylor hT P.X_continuous P.V_continuous
    P.A_continuous P.X_derivative P.V_derivative
    (P.velocity_horizon_eq_zero hT)

theorem velocity_terminal_normalized_tendsto
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    Tendsto
      (fun delta : ℝ => delta⁻¹ • P.V (T - delta))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-M.grad (P.X T))) := by
  have hslope :
      Tendsto (slope P.V T) (𝓝[<] T) (𝓝 (P.A T)) := by
    have hs :=
      hasDerivWithinAt_iff_tendsto_slope.mp
        (P.velocity_hasDerivWithinAt_horizon hT)
    simpa only [Iic_sdiff_right] using hs
  have hid : Tendsto (fun t : ℝ => t)
      (𝓝[<] T) (𝓝 T) :=
    tendsto_id.mono_left inf_le_left
  have hzero : Tendsto (fun t : ℝ => T - t)
      (𝓝[<] T) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hid :
      Tendsto (fun t : ℝ => T - t)
        (𝓝[<] T) (𝓝 (T - T)))
  have hsub :
      Tendsto (fun delta : ℝ => T - delta)
        (𝓝[>] (0 : ℝ)) (𝓝[<] T) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hdelta :
          Tendsto (fun delta : ℝ => delta)
            (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left inf_le_left
      simpa using (tendsto_const_nhds.sub hdelta :
        Tendsto (fun delta : ℝ => T - delta)
          (𝓝[>] (0 : ℝ)) (𝓝 (T - 0)))
    · filter_upwards [eventually_mem_nhdsWithin] with delta hdelta
      exact sub_lt_self T (show 0 < delta from hdelta)
  have hcomp :=
    (hslope.comp hsub).neg
  have heq :
      (fun delta : ℝ => -(slope P.V T (T - delta)))
        =ᶠ[𝓝[>] (0 : ℝ)]
      fun delta : ℝ => delta⁻¹ • P.V (T - delta) := by
    filter_upwards [eventually_mem_nhdsWithin] with delta hdelta
    have hdelta0 : delta ≠ 0 :=
      ne_of_gt (show 0 < delta from hdelta)
    simp only [slope, vsub_eq_sub,
      P.velocity_horizon_eq_zero hT, sub_zero]
    rw [← neg_smul]
    congr 1
    field_simp [hdelta0]
    ring
  have hlimit :=
    hcomp.congr' heq
  rw [P.acceleration_horizon_eq_gradient hT] at hlimit
  exact hlimit

theorem position_terminal_normalized_tendsto
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    Tendsto
      (fun delta : ℝ =>
        (delta ^ 2)⁻¹ •
          (P.X (T - delta) - P.X T))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((1 / 2 : ℝ) • M.grad (P.X T))) := by
  have hlimit :=
    quadraticLittleO_to_normalized
      (P.terminal_taylor_littleO hT).2
  rw [P.acceleration_horizon_eq_gradient hT] at hlimit
  exact hlimit

theorem objective_terminal_normalized_tendsto
    (P : ContinuousTrajectory M T x0) (hT : 0 < T) :
    Tendsto
      (fun delta : ℝ =>
        (M.f (P.X (T - delta)) - M.f (P.X T)) /
          delta ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (‖M.grad (P.X T)‖ ^ 2 / 2)) := by
  let g : E := M.grad (P.X T)
  let z : ℝ → E := fun delta =>
    (delta ^ 2)⁻¹ • (P.X (T - delta) - P.X T)
  have hz :
      Tendsto z (𝓝[>] (0 : ℝ))
        (𝓝 ((1 / 2 : ℝ) • g)) := by
    simpa [z, g] using
      P.position_terminal_normalized_tendsto hT
  have hlower :
      Tendsto (fun delta : ℝ => ⟪g, z delta⟫_ℝ)
        (𝓝[>] (0 : ℝ)) (𝓝 (‖g‖ ^ 2 / 2)) := by
    have hinner :=
      Filter.Tendsto.inner (𝕜 := ℝ)
        (tendsto_const_nhds :
          Tendsto (fun _delta : ℝ => g)
            (𝓝[>] (0 : ℝ)) (𝓝 g))
        hz
    have hinner' :
        Tendsto (fun delta : ℝ => ⟪g, z delta⟫_ℝ)
          (𝓝[>] (0 : ℝ))
          (𝓝 ((1 / 2 : ℝ) * ‖g‖ ^ 2)) := by
      simpa [real_inner_smul_right,
        real_inner_self_eq_norm_sq] using hinner
    have hcoef :
        (1 / 2 : ℝ) * ‖g‖ ^ 2 = ‖g‖ ^ 2 / 2 := by
      ring
    rw [hcoef] at hinner'
    exact hinner'
  have hdeltaSq :
      Tendsto (fun delta : ℝ => delta ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using
      ((tendsto_id.mono_left inf_le_left :
        Tendsto (fun delta : ℝ => delta)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))).pow 2)
  have hnormSq :
      Tendsto (fun delta : ℝ => ‖z delta‖ ^ 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (‖(1 / 2 : ℝ) • g‖ ^ 2)) :=
    hz.norm.pow 2
  have hresidual :
      Tendsto
        (fun delta : ℝ =>
          delta ^ 2 * ‖z delta‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Pi.mul_apply, zero_mul] using
      hdeltaSq.mul hnormSq
  have hextra :
      Tendsto
        (fun delta : ℝ =>
          ((M.L : ℝ) / 2) *
            (delta ^ 2 * ‖z delta‖ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hconst :
        Tendsto (fun _delta : ℝ => (M.L : ℝ) / 2)
          (𝓝[>] (0 : ℝ)) (𝓝 ((M.L : ℝ) / 2)) :=
      tendsto_const_nhds
    simpa only [Pi.mul_apply, mul_zero] using
      hconst.mul hresidual
  have hupper :
      Tendsto
        (fun delta : ℝ =>
          ⟪g, z delta⟫_ℝ +
            ((M.L : ℝ) / 2) *
              (delta ^ 2 * ‖z delta‖ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (‖g‖ ^ 2 / 2)) := by
    simpa only [Pi.add_apply, add_zero] using
      hlower.add hextra
  have hlowerBound :
      ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ),
        ⟪g, z delta⟫_ℝ ≤
          (M.f (P.X (T - delta)) - M.f (P.X T)) /
            delta ^ 2 := by
    filter_upwards [eventually_mem_nhdsWithin] with delta hdelta
    have hdeltaPos : 0 < delta := hdelta
    have hdeltaSqPos : 0 < delta ^ 2 := sq_pos_of_pos hdeltaPos
    have hdeltaSqNe : delta ^ 2 ≠ 0 := hdeltaSqPos.ne'
    let d : E := P.X (T - delta) - P.X T
    have hdz : d = delta ^ 2 • z delta := by
      dsimp [d, z]
      rw [smul_smul, mul_inv_cancel₀ hdeltaSqNe, one_smul]
    have hinnerD :
        ⟪g, d⟫_ℝ = delta ^ 2 * ⟪g, z delta⟫_ℝ := by
      rw [hdz, real_inner_smul_right]
    have hfirst :
        M.f (P.X T) + ⟪g, d⟫_ℝ ≤
          M.f (P.X (T - delta)) := by
      simpa [g, d] using
        M.firstOrder (P.X T) (P.X (T - delta))
    apply (le_div_iff₀ hdeltaSqPos).2
    rw [mul_comm]
    rw [hinnerD] at hfirst
    linarith
  have hupperBound :
      ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ),
        (M.f (P.X (T - delta)) - M.f (P.X T)) /
            delta ^ 2 ≤
          ⟪g, z delta⟫_ℝ +
            ((M.L : ℝ) / 2) *
              (delta ^ 2 * ‖z delta‖ ^ 2) := by
    filter_upwards [eventually_mem_nhdsWithin] with delta hdelta
    have hdeltaPos : 0 < delta := hdelta
    have hdeltaSqPos : 0 < delta ^ 2 := sq_pos_of_pos hdeltaPos
    have hdeltaSqNe : delta ^ 2 ≠ 0 := hdeltaSqPos.ne'
    let d : E := P.X (T - delta) - P.X T
    have hdz : d = delta ^ 2 • z delta := by
      dsimp [d, z]
      rw [smul_smul, mul_inv_cancel₀ hdeltaSqNe, one_smul]
    have hinnerD :
        ⟪g, d⟫_ℝ = delta ^ 2 * ⟪g, z delta⟫_ℝ := by
      rw [hdz, real_inner_smul_right]
    have hnormD :
        ‖d‖ ^ 2 =
          delta ^ 4 * ‖z delta‖ ^ 2 := by
      rw [hdz, norm_smul, Real.norm_eq_abs,
        abs_of_pos hdeltaSqPos]
      ring
    have hdescent :
        M.f (P.X (T - delta)) ≤
          M.f (P.X T) + ⟪g, d⟫_ℝ +
            ((M.L : ℝ) / 2) * ‖d‖ ^ 2 := by
      simpa [g, d] using
        M.descent (P.X T) (P.X (T - delta))
    apply (div_le_iff₀ hdeltaSqPos).2
    rw [hinnerD, hnormD] at hdescent
    calc
      M.f (P.X (T - delta)) - M.f (P.X T) ≤
          delta ^ 2 * ⟪g, z delta⟫_ℝ +
            ((M.L : ℝ) / 2) *
              (delta ^ 4 * ‖z delta‖ ^ 2) := by
        linarith
      _ =
          (⟪g, z delta⟫_ℝ +
            ((M.L : ℝ) / 2) *
              (delta ^ 2 * ‖z delta‖ ^ 2)) *
            delta ^ 2 := by ring
  have hlimit :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlower hupper hlowerBound hupperBound
  simpa [g] using hlimit

end ContinuousTrajectory

end LemniAcc
