import LemniAcc.Continuous.Trajectory

/-!
# Continuous-time Lyapunov function for LemniAcc

This module formalizes the Lyapunov function and its exact interior derivative
from the continuous-time analysis in the manuscript.  Endpoint limits and the
paper-facing rates are proved in `LemniAcc.Continuous.Convergence`.
-/

open scoped InnerProductSpace Topology
open Set
open InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

open Lemniscatic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

namespace Continuous

/-- The rescaled momentum `Z(t) = σ(t)^3 X'(t) / 4`. -/
noncomputable def momentum
    {M : SmoothConvexModel E} {x0 : E}
    (T : ℝ) (P : ContinuousTrajectory M T x0) (t : ℝ) : E :=
  (sigma T t ^ 3 / 4) • P.V t

/-- The coefficient `(1-r)^2/(2r)` in the rewritten function-value part. -/
noncomputable def terminalFunctionCoeff (T t : ℝ) : ℝ :=
  (1 - rho T t) ^ 2 / (2 * rho T t)

/-- The coefficient `(1-r^2)/(2r)` in the original function-value part. -/
noncomputable def primaryFunctionCoeff (T t : ℝ) : ℝ :=
  (1 - rho T t ^ 2) / (2 * rho T t)

/-- The coefficient `(1+r^2)/(1-r^2)` in the first squared norm. -/
noncomputable def transportCoeff (T t : ℝ) : ℝ :=
  (1 + rho T t ^ 2) / (1 - rho T t ^ 2)

/-- The first vector inside the squared-norm difference. -/
noncomputable def transportedVector
    {M : SmoothConvexModel E} {x0 : E}
    (T : ℝ) (xStar : E) (P : ContinuousTrajectory M T x0)
    (t : ℝ) : E :=
  P.X t - xStar +
    (transportCoeff T t / varpiT T) • momentum T P t

/-- The second vector inside the squared-norm difference. -/
noncomputable def terminalVector
    {M : SmoothConvexModel E} {x0 : E}
    (T : ℝ) (xStar : E) (P : ContinuousTrajectory M T x0)
    (t : ℝ) : E :=
  P.X T - xStar + (1 / varpiT T) • momentum T P t

/-- The manuscript Lyapunov function, defined on the open interval `(0,T)`.

The expression is meaningful on all real inputs in Lean, but all analytic
claims below explicitly assume `t ∈ Ioo 0 T`, where its rational
coefficients have nonzero denominators. -/
noncomputable def lyapunov
    (M : SmoothConvexModel E) (T : ℝ) (xStar x0 : E)
    (P : ContinuousTrajectory M T x0) (t : ℝ) : ℝ :=
  primaryFunctionCoeff T t *
      (M.f (P.X t) - M.f xStar)
    - terminalFunctionCoeff T t *
      (M.f (P.X T) - M.f xStar)
    + (varpiT T ^ 2 / 2) *
      (‖transportedVector T xStar P t‖ ^ 2 -
        ‖terminalVector T xStar P t‖ ^ 2)

/-- The two function-value terms in the original Lyapunov definition. -/
noncomputable def functionPart
    (M : SmoothConvexModel E) (T : ℝ) (xStar x0 : E)
    (P : ContinuousTrajectory M T x0) (t : ℝ) : ℝ :=
  primaryFunctionCoeff T t * (M.f (P.X t) - M.f xStar)
    - terminalFunctionCoeff T t * (M.f (P.X T) - M.f xStar)

/-- The difference of squared norms in the original Lyapunov definition. -/
noncomputable def squaredNormPart
    {M : SmoothConvexModel E} (T : ℝ) (xStar x0 : E)
    (P : ContinuousTrajectory M T x0) (t : ℝ) : ℝ :=
  (varpiT T ^ 2 / 2) *
    (‖transportedVector T xStar P t‖ ^ 2 -
      ‖terminalVector T xStar P t‖ ^ 2)

/-- The algebraically expanded form of the Lyapunov function used for
endpoint limits. -/
noncomputable def expandedLyapunov
    (M : SmoothConvexModel E) (T : ℝ) (xStar x0 : E)
    (P : ContinuousTrajectory M T x0) (t : ℝ) : ℝ :=
  (1 - rho T t) * (M.f (P.X t) - M.f xStar)
    + terminalFunctionCoeff T t * (M.f (P.X t) - M.f (P.X T))
    + (varpiT T ^ 2 / 2) *
      (‖P.X t - xStar‖ ^ 2 - ‖P.X T - xStar‖ ^ 2)
    + (sigma T t ^ 2 / 8) * ‖P.V t‖ ^ 2
    + (varpiT T * sigma T t * rho T t / 2) *
      ⟪P.X t - xStar, P.V t⟫_ℝ
    + (varpiT T * sigma T t ^ 3 / 4) *
      ⟪P.X t - P.X T, P.V t⟫_ℝ

private theorem one_sub_rho_hasDerivAt
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun u : ℝ => 1 - rho T u)
      (varpiT T * sigma T t * rho T t) t := by
  simpa using (rho_hasDerivAt_sigma hT ht).const_sub 1

private theorem terminalFunctionCoeff_hasDerivAt
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (terminalFunctionCoeff T)
      (varpiT T * sigma T t ^ 3 / 2) t := by
  let r : ℝ := rho T t
  let s : ℝ := sigma T t
  let v : ℝ := varpiT T
  let rp : ℝ := -v * s * r
  have hr : 0 < r := by
    simpa [r] using (rho_pos_lt_one hT ht).1
  have hrd : HasDerivAt (rho T) rp t := by
    simpa [rp, r, s, v] using rho_hasDerivAt_sigma hT ht
  have hone :
      HasDerivAt (fun u : ℝ => 1 - rho T u) (-rp) t := by
    simpa using hrd.const_sub 1
  have hnum :
      HasDerivAt (fun u : ℝ => (1 - rho T u) ^ 2)
        (2 * (1 - r) * (-rp)) t := by
    simpa [r] using! hone.pow 2
  have hden :
      HasDerivAt (fun u : ℝ => 2 * rho T u) (2 * rp) t := by
    simpa using hrd.const_mul 2
  have hraw :
      HasDerivAt (terminalFunctionCoeff T)
        ((2 * (1 - r) * (-rp) * (2 * r) -
            (1 - r) ^ 2 * (2 * rp)) /
          (2 * r) ^ 2) t := by
    simpa [terminalFunctionCoeff, r] using!
      hnum.div hden (mul_ne_zero (by norm_num) hr.ne')
  have hs2 : s ^ 2 = r⁻¹ - r := by
    simpa [s, r] using sigma_sq_eq_inv_sub hT ht
  have hcoef :
      (2 * (1 - r) * (-rp) * (2 * r) -
            (1 - r) ^ 2 * (2 * rp)) /
          (2 * r) ^ 2 =
        v * s ^ 3 / 2 := by
    dsimp [rp]
    have hpoly : 1 - r ^ 2 = s ^ 2 * r := by
      rw [hs2]
      field_simp [hr.ne']
    calc
      (2 * (1 - r) * (-(-v * s * r)) * (2 * r) -
              (1 - r) ^ 2 * (2 * (-v * s * r))) /
            (2 * r) ^ 2 =
          v * s * (1 - r ^ 2) / (2 * r) := by
            field_simp [hr.ne']
            ring
      _ = v * s ^ 3 / 2 := by
            rw [hpoly]
            field_simp [hr.ne']
  rw [← hcoef]
  simpa [v, s] using hraw

private theorem primaryFunctionCoeff_hasDerivAt
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (primaryFunctionCoeff T)
      (varpiT T * sigma T t * rho T t +
        varpiT T * sigma T t ^ 3 / 2) t := by
  let r : ℝ := rho T t
  let s : ℝ := sigma T t
  let v : ℝ := varpiT T
  let rp : ℝ := -v * s * r
  have hr : 0 < r := by
    simpa [r] using (rho_pos_lt_one hT ht).1
  have hrd : HasDerivAt (rho T) rp t := by
    simpa [rp, r, s, v] using rho_hasDerivAt_sigma hT ht
  have hnum :
      HasDerivAt (fun u : ℝ => 1 - rho T u ^ 2)
        (-2 * r * rp) t := by
    simpa [r] using! (hrd.pow 2).const_sub 1
  have hden :
      HasDerivAt (fun u : ℝ => 2 * rho T u) (2 * rp) t := by
    simpa using hrd.const_mul 2
  have hraw :
      HasDerivAt (primaryFunctionCoeff T)
        (((-2 * r * rp) * (2 * r) -
            (1 - r ^ 2) * (2 * rp)) /
          (2 * r) ^ 2) t := by
    simpa [primaryFunctionCoeff, r] using!
      hnum.div hden (mul_ne_zero (by norm_num) hr.ne')
  have hs2 : s ^ 2 = r⁻¹ - r := by
    simpa [s, r] using sigma_sq_eq_inv_sub hT ht
  have hpoly : 1 - r ^ 2 = s ^ 2 * r := by
    rw [hs2]
    field_simp [hr.ne']
  have hcoef :
      ((-2 * r * rp) * (2 * r) -
            (1 - r ^ 2) * (2 * rp)) /
          (2 * r) ^ 2 =
        v * s * r + v * s ^ 3 / 2 := by
    dsimp [rp]
    calc
      ((-2 * r * (-v * s * r)) * (2 * r) -
              (1 - r ^ 2) * (2 * (-v * s * r))) /
            (2 * r) ^ 2 =
          v * s * (1 + r ^ 2) / (2 * r) := by
            field_simp [hr.ne']
            ring
      _ = v * s * r + v * s ^ 3 / 2 := by
            rw [show 1 + r ^ 2 = 2 * r ^ 2 + s ^ 2 * r by
              nlinarith [hpoly]]
            field_simp [hr.ne']
  rw [← hcoef]
  simpa [v, s, r] using hraw

private theorem transportCoeff_hasDerivAt
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (transportCoeff T)
      (-4 * varpiT T / sigma T t ^ 3) t := by
  let r : ℝ := rho T t
  let s : ℝ := sigma T t
  let v : ℝ := varpiT T
  let rp : ℝ := -v * s * r
  have hr : 0 < r ∧ r < 1 := by
    simpa [r] using rho_pos_lt_one hT ht
  have hs : 0 < s := by
    simpa [s] using sigma_pos hT ht
  have hrd : HasDerivAt (rho T) rp t := by
    simpa [rp, r, s, v] using rho_hasDerivAt_sigma hT ht
  have hnum :
      HasDerivAt (fun u : ℝ => 1 + rho T u ^ 2)
        (2 * r * rp) t := by
    simpa [r] using! (hrd.pow 2).const_add 1
  have hden :
      HasDerivAt (fun u : ℝ => 1 - rho T u ^ 2)
        (-2 * r * rp) t := by
    simpa [r] using! (hrd.pow 2).const_sub 1
  have hdenne : 1 - r ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg r]
  have hraw :
      HasDerivAt (transportCoeff T)
        (((2 * r * rp) * (1 - r ^ 2) -
            (1 + r ^ 2) * (-2 * r * rp)) /
          (1 - r ^ 2) ^ 2) t := by
    simpa [transportCoeff, r] using! hnum.div hden hdenne
  have hs2 : s ^ 2 = r⁻¹ - r := by
    simpa [s, r] using sigma_sq_eq_inv_sub hT ht
  have hcoef :
      ((2 * r * rp) * (1 - r ^ 2) -
            (1 + r ^ 2) * (-2 * r * rp)) /
          (1 - r ^ 2) ^ 2 =
        -4 * v / s ^ 3 := by
    dsimp [rp]
    have hpoly : 1 - r ^ 2 = s ^ 2 * r := by
      rw [hs2]
      field_simp [hr.1.ne']
    calc
      ((2 * r * (-v * s * r)) * (1 - r ^ 2) -
              (1 + r ^ 2) * (-2 * r * (-v * s * r))) /
            (1 - r ^ 2) ^ 2 =
          -4 * v * s * r ^ 2 / (1 - r ^ 2) ^ 2 := by ring
      _ = -4 * v / s ^ 3 := by
            rw [hpoly]
            field_simp [hr.1.ne', hs.ne']
  rw [← hcoef]
  simpa [v, s] using hraw

/-- The ODE makes the momentum derivative exactly
`-(σ(t)^3/2) ∇f(X(t))`. -/
theorem momentum_hasDerivAt
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (P : ContinuousTrajectory M T x0) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (momentum T P)
      ((-(sigma T t ^ 3 / 2)) • M.grad (P.X t)) t := by
  let s : ℝ := sigma T t
  let sd : ℝ := sigmaDot T t
  have hs : 0 < s := by
    simpa [s] using sigma_pos hT ht
  have hsigma : HasDerivAt (sigma T) sd t := by
    simpa [sd] using sigma_hasDerivAt hT ht
  have hscalar :
      HasDerivAt (fun u : ℝ => sigma T u ^ 3 / 4)
        (3 * s ^ 2 * sd / 4) t := by
    simpa [s] using! (hsigma.pow 3).div_const 4
  have hraw :
      HasDerivAt (momentum T P)
        ((s ^ 3 / 4) • P.A t +
          (3 * s ^ 2 * sd / 4) • P.V t) t := by
    simpa [momentum, s] using! hscalar.smul (P.V_derivative t ht)
  have hA :
      P.A t = -(gamma T t) • P.V t - 2 • M.grad (P.X t) := by
    have hode := P.ode t ht
    calc
      P.A t =
          (P.A t + gamma T t • P.V t + 2 • M.grad (P.X t)) -
            gamma T t • P.V t - 2 • M.grad (P.X t) := by abel
      _ = -(gamma T t) • P.V t - 2 • M.grad (P.X t) := by
            rw [hode]
            simp
  have hcoef :
      (s ^ 3 / 4) • P.A t +
          (3 * s ^ 2 * sd / 4) • P.V t =
        (-(s ^ 3 / 2)) • M.grad (P.X t) := by
    have hcancel :
        (s ^ 3 / 4) * (-(3 * sd / s)) +
            3 * s ^ 2 * sd / 4 = 0 := by
      field_simp [hs.ne']
      ring
    have hgrad :
        (s ^ 3 / 4) * (-2) = -(s ^ 3 / 2) := by ring
    have hgamma : gamma T t = 3 * sd / s := by
      rfl
    rw [hA, hgamma]
    calc
      (s ^ 3 / 4) •
              ((-(3 * sd / s)) • P.V t - 2 • M.grad (P.X t)) +
            (3 * s ^ 2 * sd / 4) • P.V t =
          ((s ^ 3 / 4) * (-(3 * sd / s)) +
              3 * s ^ 2 * sd / 4) • P.V t +
            ((s ^ 3 / 4) * (-2)) • M.grad (P.X t) := by module
      _ = (-(s ^ 3 / 2)) • M.grad (P.X t) := by
            rw [hcancel, hgrad]
            simp
  rw [← hcoef]
  simpa [s] using hraw

private theorem objective_hasDerivAt
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (P : ContinuousTrajectory M T x0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun u : ℝ => M.f (P.X u))
      ⟪M.grad (P.X t), P.V t⟫_ℝ t := by
  change HasDerivAt (M.f ∘ P.X)
    ⟪M.grad (P.X t), P.V t⟫_ℝ t
  simpa only [toDual_apply_apply] using
    (M.hasGradient (P.X t)).hasFDerivAt.comp_hasDerivAt
      t (P.X_derivative t ht)

/-- The transported vector has the derivative left after the position and
momentum-transport terms cancel. -/
theorem transportedVector_hasDerivAt
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (transportedVector T xStar P)
      ((transportCoeff T t / varpiT T) •
        ((-(sigma T t ^ 3 / 2)) • M.grad (P.X t))) t := by
  let s : ℝ := sigma T t
  let v : ℝ := varpiT T
  have hs : 0 < s := by
    simpa [s] using sigma_pos hT ht
  have hv : 0 < v := by
    simpa [v] using varpiT_pos hT
  have hcoeff0 := transportCoeff_hasDerivAt hT ht
  have hcoeff :
      HasDerivAt (fun u : ℝ => transportCoeff T u / v)
        (-4 / s ^ 3) t := by
    have hraw := hcoeff0.div_const v
    change
      HasDerivAt (fun u : ℝ => transportCoeff T u / v)
        ((-4 * v / s ^ 3) / v) t at hraw
    have heq : (-4 * v / s ^ 3) / v = -4 / s ^ 3 := by
      field_simp [hv.ne']
    rw [heq] at hraw
    exact hraw
  have hZ := momentum_hasDerivAt P hT ht
  have hsmul :
      HasDerivAt
        (fun u : ℝ =>
          (transportCoeff T u / v) • momentum T P u)
        ((transportCoeff T t / v) •
            ((-(s ^ 3 / 2)) • M.grad (P.X t)) +
          (-4 / s ^ 3) • momentum T P t) t := by
    simpa [v, s] using! hcoeff.smul hZ
  have hraw :
      HasDerivAt (transportedVector T xStar P)
        (P.V t +
          ((transportCoeff T t / v) •
              ((-(s ^ 3 / 2)) • M.grad (P.X t)) +
            (-4 / s ^ 3) • momentum T P t)) t := by
    simpa [transportedVector, v] using!
      (P.X_derivative t ht).sub_const xStar |>.add hsmul
  have hcancel :
      P.V t + (-4 / s ^ 3) • momentum T P t = 0 := by
    rw [momentum]
    change
      P.V t + (-4 / s ^ 3) • ((s ^ 3 / 4) • P.V t) = 0
    have hc : (-4 / s ^ 3) * (s ^ 3 / 4) = (-1 : ℝ) := by
      field_simp [hs.ne']
    rw [smul_smul, hc]
    simp
  have hderiv :
      P.V t +
          ((transportCoeff T t / v) •
              ((-(s ^ 3 / 2)) • M.grad (P.X t)) +
            (-4 / s ^ 3) • momentum T P t) =
        (transportCoeff T t / v) •
          ((-(s ^ 3 / 2)) • M.grad (P.X t)) := by
    calc
      P.V t +
            ((transportCoeff T t / v) •
                ((-(s ^ 3 / 2)) • M.grad (P.X t)) +
              (-4 / s ^ 3) • momentum T P t) =
          (P.V t + (-4 / s ^ 3) • momentum T P t) +
            (transportCoeff T t / v) •
              ((-(s ^ 3 / 2)) • M.grad (P.X t)) := by abel
      _ = (transportCoeff T t / v) •
          ((-(s ^ 3 / 2)) • M.grad (P.X t)) := by rw [hcancel, zero_add]
  rw [← hderiv]
  simpa [v, s] using hraw

/-- The terminal vector only varies through the momentum. -/
theorem terminalVector_hasDerivAt
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (terminalVector T xStar P)
      ((1 / varpiT T) •
        ((-(sigma T t ^ 3 / 2)) • M.grad (P.X t))) t := by
  have hZ := momentum_hasDerivAt P hT ht
  unfold terminalVector
  have hraw :=
    (hasDerivAt_const t (P.X T - xStar)).add
      (hZ.const_smul (1 / varpiT T))
  have hraw' :
      HasDerivAt
        ((fun _u : ℝ => P.X T - xStar) +
          (1 / varpiT T) • momentum T P)
        ((1 / varpiT T) •
          ((-(sigma T t ^ 3 / 2)) • M.grad (P.X t))) t :=
    hraw.congr_deriv (by simp)
  apply hraw'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun u => by simp

omit [CompleteSpace E] in
private theorem norm_sq_hasDerivAt
    {Y : ℝ → E} {Y' : E} {t : ℝ}
    (hY : HasDerivAt Y Y' t) :
    HasDerivAt (fun u : ℝ => ‖Y u‖ ^ 2)
      (2 * ⟪Y t, Y'⟫_ℝ) t := by
  have hinner := hY.inner ℝ hY
  simpa only [real_inner_self_eq_norm_sq, real_inner_comm Y' (Y t),
    two_mul] using hinner

private theorem functionPart_hasDerivAt
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (functionPart M T xStar x0 P)
      (varpiT T * sigma T t * rho T t *
          (M.f (P.X t) - M.f xStar)
        + (varpiT T * sigma T t ^ 3 / 2) *
          (M.f (P.X t) - M.f (P.X T))
        + (2 / sigma T t) *
          ⟪momentum T P t, M.grad (P.X t)⟫_ℝ) t := by
  let r : ℝ := rho T t
  let s : ℝ := sigma T t
  let v : ℝ := varpiT T
  let gdot : ℝ := ⟪M.grad (P.X t), P.V t⟫_ℝ
  have hr : 0 < r := by
    simpa [r] using (rho_pos_lt_one hT ht).1
  have hs : 0 < s := by
    simpa [s] using sigma_pos hT ht
  have hprimary := primaryFunctionCoeff_hasDerivAt hT ht
  have hterminal := terminalFunctionCoeff_hasDerivAt hT ht
  have hf : HasDerivAt (fun u : ℝ => M.f (P.X u)) gdot t := by
    simpa [gdot] using objective_hasDerivAt P ht
  have hfirst :
      HasDerivAt
        (fun u : ℝ =>
          primaryFunctionCoeff T u * (M.f (P.X u) - M.f xStar))
        ((v * s * r + v * s ^ 3 / 2) *
            (M.f (P.X t) - M.f xStar) +
          primaryFunctionCoeff T t * gdot) t := by
    simpa [v, s, r, gdot] using!
      hprimary.mul (hf.sub_const (M.f xStar))
  have hsecond :
      HasDerivAt
        (fun u : ℝ =>
          terminalFunctionCoeff T u *
            (M.f (P.X T) - M.f xStar))
        ((v * s ^ 3 / 2) *
          (M.f (P.X T) - M.f xStar)) t := by
    simpa [v, s] using!
      hterminal.mul_const (M.f (P.X T) - M.f xStar)
  have hraw :
      HasDerivAt (functionPart M T xStar x0 P)
        ((v * s * r + v * s ^ 3 / 2) *
              (M.f (P.X t) - M.f xStar) +
            primaryFunctionCoeff T t * gdot -
          (v * s ^ 3 / 2) *
            (M.f (P.X T) - M.f xStar)) t := by
    unfold functionPart
    have hsub := hfirst.sub hsecond
    apply hsub.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun u => by simp
  have hs2 : s ^ 2 = r⁻¹ - r := by
    simpa [s, r] using sigma_sq_eq_inv_sub hT ht
  have hprimaryValue :
      primaryFunctionCoeff T t = s ^ 2 / 2 := by
    unfold primaryFunctionCoeff
    change (1 - r ^ 2) / (2 * r) = s ^ 2 / 2
    rw [hs2]
    field_simp [hr.ne']
  have hmomentumInner :
      (2 / s) * ⟪momentum T P t, M.grad (P.X t)⟫_ℝ =
        (s ^ 2 / 2) * gdot := by
    rw [momentum]
    simp only [real_inner_smul_left]
    change
      (2 / s) * ((s ^ 3 / 4) *
        ⟪P.V t, M.grad (P.X t)⟫_ℝ) =
      (s ^ 2 / 2) * ⟪M.grad (P.X t), P.V t⟫_ℝ
    rw [real_inner_comm (P.V t) (M.grad (P.X t))]
    field_simp [hs.ne']
    ring
  have hcoef :
      (v * s * r + v * s ^ 3 / 2) *
              (M.f (P.X t) - M.f xStar) +
            primaryFunctionCoeff T t * gdot -
          (v * s ^ 3 / 2) *
            (M.f (P.X T) - M.f xStar) =
        v * s * r * (M.f (P.X t) - M.f xStar)
          + (v * s ^ 3 / 2) *
            (M.f (P.X t) - M.f (P.X T))
          + (2 / s) *
            ⟪momentum T P t, M.grad (P.X t)⟫_ℝ := by
    rw [hprimaryValue, hmomentumInner]
    ring
  rw [← hcoef]
  simpa [v, s, r] using hraw

/-- The derivative of the squared-norm part in the form used in the
manuscript calculation. -/
theorem squaredNormPart_hasDerivAt
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (squaredNormPart T xStar x0 P)
      (-varpiT T * sigma T t * rho T t *
          ⟪P.X t - xStar, M.grad (P.X t)⟫_ℝ
        - (varpiT T * sigma T t ^ 3 / 2) *
          ⟪P.X t - P.X T, M.grad (P.X t)⟫_ℝ
        - (2 / sigma T t) *
          ⟪momentum T P t, M.grad (P.X t)⟫_ℝ) t := by
  let r : ℝ := rho T t
  let s : ℝ := sigma T t
  let v : ℝ := varpiT T
  let q : ℝ := transportCoeff T t
  let G : E := M.grad (P.X t)
  let Z : E := momentum T P t
  let U : E := P.X t - xStar
  let W : E := P.X T - xStar
  let Zp : E := (-(s ^ 3 / 2)) • G
  have hr : 0 < r ∧ r < 1 := by
    simpa [r] using rho_pos_lt_one hT ht
  have hs : 0 < s := by
    simpa [s] using sigma_pos hT ht
  have hv : 0 < v := by
    simpa [v] using varpiT_pos hT
  have hY := transportedVector_hasDerivAt xStar P hT ht
  have hW := terminalVector_hasDerivAt xStar P hT ht
  have hY' :
      HasDerivAt (transportedVector T xStar P)
        ((q / v) • Zp) t := by
    simpa [q, v, s, G, Zp] using hY
  have hW' :
      HasDerivAt (terminalVector T xStar P)
        ((1 / v) • Zp) t := by
    simpa [v, s, G, Zp] using hW
  have hnormY := norm_sq_hasDerivAt hY'
  have hnormW := norm_sq_hasDerivAt hW'
  have hdiff := hnormY.sub hnormW
  have hscaled := hdiff.const_mul (v ^ 2 / 2)
  have hraw :
      HasDerivAt (squaredNormPart T xStar x0 P)
        ((v ^ 2 / 2) *
          (2 * ⟪transportedVector T xStar P t, (q / v) • Zp⟫_ℝ -
            2 * ⟪terminalVector T xStar P t, (1 / v) • Zp⟫_ℝ)) t := by
    unfold squaredNormPart
    apply hscaled.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun u => by simp [v]
  have hpoly : 1 - r ^ 2 = s ^ 2 * r := by
    have hs2 : s ^ 2 = r⁻¹ - r := by
      simpa [s, r] using sigma_sq_eq_inv_sub hT ht
    rw [hs2]
    field_simp [hr.1.ne']
  have hq1 :
      q * s ^ 3 / 2 = s * r + s ^ 3 / 2 := by
    dsimp [q, transportCoeff]
    change
      (1 + r ^ 2) / (1 - r ^ 2) * s ^ 3 / 2 =
        s * r + s ^ 3 / 2
    rw [hpoly]
    field_simp [hr.1.ne', hs.ne']
    nlinarith [hpoly]
  have hq2 :
      (q ^ 2 - 1) * s ^ 3 / 2 = 2 / s := by
    have hpolySq :=
      congrArg (fun z : ℝ => z ^ 2) hpoly
    dsimp [q, transportCoeff]
    change
      (((1 + r ^ 2) / (1 - r ^ 2)) ^ 2 - 1) *
          s ^ 3 / 2 = 2 / s
    rw [hpoly]
    field_simp [hr.1.ne', hs.ne']
    nlinarith [hpolySq]
  have hrawValue :
      (v ^ 2 / 2) *
          (2 * ⟪transportedVector T xStar P t, (q / v) • Zp⟫_ℝ -
            2 * ⟪terminalVector T xStar P t, (1 / v) • Zp⟫_ℝ) =
        v * q * ⟪U, Zp⟫_ℝ - v * ⟪W, Zp⟫_ℝ +
          (q ^ 2 - 1) * ⟪Z, Zp⟫_ℝ := by
    change
      (v ^ 2 / 2) *
          (2 * ⟪U + (q / v) • Z, (q / v) • Zp⟫_ℝ -
            2 * ⟪W + (1 / v) • Z, (1 / v) • Zp⟫_ℝ) =
        v * q * ⟪U, Zp⟫_ℝ - v * ⟪W, Zp⟫_ℝ +
          (q ^ 2 - 1) * ⟪Z, Zp⟫_ℝ
    simp only [inner_add_left, real_inner_smul_left,
      real_inner_smul_right]
    field_simp [hv.ne']
    ring
  have hposition :
      ⟪P.X t - P.X T, G⟫_ℝ = ⟪U, G⟫_ℝ - ⟪W, G⟫_ℝ := by
    have hx :
        P.X t - P.X T =
          (P.X t - xStar) - (P.X T - xStar) := by abel
    rw [hx, inner_sub_left]
  have hcoef :
      (v ^ 2 / 2) *
          (2 * ⟪transportedVector T xStar P t, (q / v) • Zp⟫_ℝ -
            2 * ⟪terminalVector T xStar P t, (1 / v) • Zp⟫_ℝ) =
        -v * s * r * ⟪U, G⟫_ℝ
          - (v * s ^ 3 / 2) * ⟪P.X t - P.X T, G⟫_ℝ
          - (2 / s) * ⟪Z, G⟫_ℝ := by
    rw [hrawValue]
    dsimp [Zp]
    simp only [real_inner_smul_right]
    calc
      v * q * (-(s ^ 3 / 2) * ⟪U, G⟫_ℝ) -
              v * (-(s ^ 3 / 2) * ⟪W, G⟫_ℝ) +
              (q ^ 2 - 1) * (-(s ^ 3 / 2) * ⟪Z, G⟫_ℝ) =
          -(v * (q * s ^ 3 / 2)) * ⟪U, G⟫_ℝ +
            (v * s ^ 3 / 2) * ⟪W, G⟫_ℝ -
            ((q ^ 2 - 1) * s ^ 3 / 2) * ⟪Z, G⟫_ℝ := by ring
      _ = -v * s * r * ⟪U, G⟫_ℝ
          - (v * s ^ 3 / 2) * ⟪P.X t - P.X T, G⟫_ℝ
          - (2 / s) * ⟪Z, G⟫_ℝ := by
            rw [hq1, hq2, hposition]
            ring
  rw [← hcoef]
  simpa [v, s, r, U, G, Z] using hraw

/-- The exact Lyapunov derivative is the negative weighted sum of the two
correctly oriented Bregman divergences `D_f(xStar,X(t))` and
`D_f(X(T),X(t))`. -/
theorem lyapunov_hasDerivAt
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (lyapunov M T xStar x0 P)
      (-varpiT T * sigma T t * rho T t *
          M.bregman xStar (P.X t)
        - (varpiT T * sigma T t ^ 3 / 2) *
          M.bregman (P.X T) (P.X t)) t := by
  let v : ℝ := varpiT T
  let s : ℝ := sigma T t
  let r : ℝ := rho T t
  let X : E := P.X t
  let XT : E := P.X T
  let G : E := M.grad X
  have hA := functionPart_hasDerivAt xStar P hT ht
  have hB := squaredNormPart_hasDerivAt xStar P hT ht
  have hsum := hA.add hB
  have hraw :
      HasDerivAt (lyapunov M T xStar x0 P)
        (v * s * r * (M.f X - M.f xStar)
          + (v * s ^ 3 / 2) * (M.f X - M.f XT)
          + (2 / s) * ⟪momentum T P t, G⟫_ℝ
          + (-v * s * r * ⟪X - xStar, G⟫_ℝ
            - (v * s ^ 3 / 2) * ⟪X - XT, G⟫_ℝ
            - (2 / s) * ⟪momentum T P t, G⟫_ℝ)) t := by
    have hsum' :
        HasDerivAt
          (functionPart M T xStar x0 P +
            squaredNormPart T xStar x0 P)
          (v * s * r * (M.f X - M.f xStar)
            + (v * s ^ 3 / 2) * (M.f X - M.f XT)
            + (2 / s) * ⟪momentum T P t, G⟫_ℝ
            + (-v * s * r * ⟪X - xStar, G⟫_ℝ
              - (v * s ^ 3 / 2) * ⟪X - XT, G⟫_ℝ
              - (2 / s) * ⟪momentum T P t, G⟫_ℝ)) t := by
      simpa [v, s, r, X, XT, G] using hsum
    apply hsum'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun u => by
      simp [lyapunov, functionPart, squaredNormPart]
  have hcoef :
      v * s * r * (M.f X - M.f xStar)
          + (v * s ^ 3 / 2) * (M.f X - M.f XT)
          + (2 / s) * ⟪momentum T P t, G⟫_ℝ
          + (-v * s * r * ⟪X - xStar, G⟫_ℝ
            - (v * s ^ 3 / 2) * ⟪X - XT, G⟫_ℝ
            - (2 / s) * ⟪momentum T P t, G⟫_ℝ) =
        -v * s * r * M.bregman xStar X
          - (v * s ^ 3 / 2) * M.bregman XT X := by
    unfold SmoothConvexModel.bregman
    simp only [inner_sub_left]
    ring
  exact hraw.congr_deriv (by simpa [v, s, r, X, XT] using hcoef)

/-- Pointwise derivative identity extracted from `lyapunov_hasDerivAt`. -/
theorem lyapunov_deriv_eq
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    deriv (lyapunov M T xStar x0 P) t =
      -varpiT T * sigma T t * rho T t *
          M.bregman xStar (P.X t)
        - (varpiT T * sigma T t ^ 3 / 2) *
          M.bregman (P.X T) (P.X t) :=
  (lyapunov_hasDerivAt xStar P hT ht).deriv

private theorem bregman_nonneg
    (M : SmoothConvexModel E) (x y : E) :
    0 ≤ M.bregman x y := by
  have hsupport := M.firstOrder y x
  rw [real_inner_comm (x - y) (M.grad y)] at hsupport
  unfold SmoothConvexModel.bregman
  linarith

/-- Convexity makes the exact Lyapunov derivative nonpositive. -/
theorem lyapunov_deriv_nonpos
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    deriv (lyapunov M T xStar x0 P) t ≤ 0 := by
  rw [lyapunov_deriv_eq xStar P hT ht]
  have hv : 0 < varpiT T := varpiT_pos hT
  have hs : 0 < sigma T t := sigma_pos hT ht
  have hr : 0 < rho T t := (rho_pos_lt_one hT ht).1
  have hDstar := bregman_nonneg M xStar (P.X t)
  have hDT := bregman_nonneg M (P.X T) (P.X t)
  have hc1 :
      0 ≤ varpiT T * sigma T t * rho T t := by positivity
  have hc2 :
      0 ≤ varpiT T * sigma T t ^ 3 / 2 := by positivity
  have hsum :=
    add_nonneg (mul_nonneg hc1 hDstar) (mul_nonneg hc2 hDT)
  linarith

/-- On the open time interval, the original squared-norm definition equals
the expanded expression used to take endpoint limits. -/
theorem lyapunov_eq_expanded
    {M : SmoothConvexModel E} {T : ℝ} {x0 : E}
    (xStar : E) (P : ContinuousTrajectory M T x0) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    lyapunov M T xStar x0 P t =
      expandedLyapunov M T xStar x0 P t := by
  let r : ℝ := rho T t
  let s : ℝ := sigma T t
  let v : ℝ := varpiT T
  let q : ℝ := transportCoeff T t
  let U : E := P.X t - xStar
  let W : E := P.X T - xStar
  let Z : E := momentum T P t
  have hr : 0 < r ∧ r < 1 := by
    simpa [r] using rho_pos_lt_one hT ht
  have hs : 0 < s := by
    simpa [s] using sigma_pos hT ht
  have hv : 0 < v := by
    simpa [v] using varpiT_pos hT
  have hs2 : s ^ 2 = r⁻¹ - r := by
    simpa [s, r] using sigma_sq_eq_inv_sub hT ht
  have hpoly : 1 - r ^ 2 = s ^ 2 * r := by
    rw [hs2]
    field_simp [hr.1.ne']
  have hprimary :
      primaryFunctionCoeff T t =
        1 - r + terminalFunctionCoeff T t := by
    unfold primaryFunctionCoeff terminalFunctionCoeff
    change
      (1 - r ^ 2) / (2 * r) =
        1 - r + (1 - r) ^ 2 / (2 * r)
    field_simp [hr.1.ne']
    ring
  have hfunction :
      primaryFunctionCoeff T t *
            (M.f (P.X t) - M.f xStar)
          - terminalFunctionCoeff T t *
            (M.f (P.X T) - M.f xStar) =
        (1 - r) * (M.f (P.X t) - M.f xStar)
          + terminalFunctionCoeff T t *
            (M.f (P.X t) - M.f (P.X T)) := by
    rw [hprimary]
    ring
  have hq1 :
      q * s ^ 3 / 2 = s * r + s ^ 3 / 2 := by
    dsimp [q, transportCoeff]
    change
      (1 + r ^ 2) / (1 - r ^ 2) * s ^ 3 / 2 =
        s * r + s ^ 3 / 2
    rw [hpoly]
    field_simp [hr.1.ne', hs.ne']
    nlinarith [hpoly]
  have hpolySq :=
    congrArg (fun z : ℝ => z ^ 2) hpoly
  have hq2 :
      (q ^ 2 - 1) * s ^ 3 / 2 = 2 / s := by
    dsimp [q, transportCoeff]
    change
      (((1 + r ^ 2) / (1 - r ^ 2)) ^ 2 - 1) *
          s ^ 3 / 2 = 2 / s
    rw [hpoly]
    field_simp [hr.1.ne', hs.ne']
    nlinarith [hpolySq]
  have hqcross :
      q * s ^ 3 / 4 = s * r / 2 + s ^ 3 / 4 := by
    calc
      q * s ^ 3 / 4 = (q * s ^ 3 / 2) / 2 := by ring
      _ = (s * r + s ^ 3 / 2) / 2 := by rw [hq1]
      _ = s * r / 2 + s ^ 3 / 4 := by ring
  have hq2poly : (q ^ 2 - 1) * s ^ 4 = 4 := by
    have h := hq2
    field_simp [hs.ne'] at h
    nlinarith
  have hqnorm :
      ((q ^ 2 - 1) / 2) * (s ^ 3 / 4) ^ 2 = s ^ 2 / 8 := by
    calc
      ((q ^ 2 - 1) / 2) * (s ^ 3 / 4) ^ 2 =
          (s ^ 2 / 8) * ((q ^ 2 - 1) * s ^ 4 / 4) := by ring
      _ = s ^ 2 / 8 := by rw [hq2poly]; ring
  have hnormRaw :
      squaredNormPart T xStar x0 P t =
        (v ^ 2 / 2) * (‖U‖ ^ 2 - ‖W‖ ^ 2)
          + v * q * ⟪U, Z⟫_ℝ - v * ⟪W, Z⟫_ℝ
          + ((q ^ 2 - 1) / 2) * ‖Z‖ ^ 2 := by
    unfold squaredNormPart
    change
      (v ^ 2 / 2) *
          (‖U + (q / v) • Z‖ ^ 2 -
            ‖W + (1 / v) • Z‖ ^ 2) =
        (v ^ 2 / 2) * (‖U‖ ^ 2 - ‖W‖ ^ 2)
          + v * q * ⟪U, Z⟫_ℝ - v * ⟪W, Z⟫_ℝ
          + ((q ^ 2 - 1) / 2) * ‖Z‖ ^ 2
    rw [norm_add_sq_real, norm_add_sq_real]
    simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    field_simp [hv.ne']
    ring
  have hUZ :
      ⟪U, Z⟫_ℝ = (s ^ 3 / 4) * ⟪U, P.V t⟫_ℝ := by
    dsimp [Z]
    rw [momentum]
    simp only [real_inner_smul_right]
    rfl
  have hWZ :
      ⟪W, Z⟫_ℝ = (s ^ 3 / 4) * ⟪W, P.V t⟫_ℝ := by
    dsimp [Z]
    rw [momentum]
    simp only [real_inner_smul_right]
    rfl
  have hnormZ :
      ‖Z‖ ^ 2 = (s ^ 3 / 4) ^ 2 * ‖P.V t‖ ^ 2 := by
    dsimp [Z]
    rw [momentum, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < s ^ 3 / 4)]
    ring
  have hposition :
      ⟪P.X t - P.X T, P.V t⟫_ℝ =
        ⟪U, P.V t⟫_ℝ - ⟪W, P.V t⟫_ℝ := by
    have hx :
        P.X t - P.X T =
          (P.X t - xStar) - (P.X T - xStar) := by abel
    rw [hx, inner_sub_left]
  have hnorm :
      squaredNormPart T xStar x0 P t =
        (v ^ 2 / 2) * (‖U‖ ^ 2 - ‖W‖ ^ 2)
          + (s ^ 2 / 8) * ‖P.V t‖ ^ 2
          + (v * s * r / 2) * ⟪U, P.V t⟫_ℝ
          + (v * s ^ 3 / 4) *
            ⟪P.X t - P.X T, P.V t⟫_ℝ := by
    rw [hnormRaw, hUZ, hWZ, hnormZ, hposition]
    calc
      v ^ 2 / 2 * (‖U‖ ^ 2 - ‖W‖ ^ 2) +
              v * q * (s ^ 3 / 4 * ⟪U, P.V t⟫_ℝ) -
              v * (s ^ 3 / 4 * ⟪W, P.V t⟫_ℝ) +
              (q ^ 2 - 1) / 2 *
                ((s ^ 3 / 4) ^ 2 * ‖P.V t‖ ^ 2) =
          v ^ 2 / 2 * (‖U‖ ^ 2 - ‖W‖ ^ 2) +
              (v * (q * s ^ 3 / 4)) * ⟪U, P.V t⟫_ℝ -
              (v * s ^ 3 / 4) * ⟪W, P.V t⟫_ℝ +
              (((q ^ 2 - 1) / 2) * (s ^ 3 / 4) ^ 2) *
                ‖P.V t‖ ^ 2 := by ring
      _ = v ^ 2 / 2 * (‖U‖ ^ 2 - ‖W‖ ^ 2)
          + (s ^ 2 / 8) * ‖P.V t‖ ^ 2
          + (v * s * r / 2) * ⟪U, P.V t⟫_ℝ
          + (v * s ^ 3 / 4) *
            (⟪U, P.V t⟫_ℝ - ⟪W, P.V t⟫_ℝ) := by
            rw [hqcross, hqnorm]
            ring
  unfold lyapunov expandedLyapunov
  rw [hfunction]
  change
    (1 - r) * (M.f (P.X t) - M.f xStar) +
          terminalFunctionCoeff T t *
            (M.f (P.X t) - M.f (P.X T)) +
          squaredNormPart T xStar x0 P t =
      (1 - r) * (M.f (P.X t) - M.f xStar) +
          terminalFunctionCoeff T t *
            (M.f (P.X t) - M.f (P.X T)) +
          (v ^ 2 / 2) * (‖U‖ ^ 2 - ‖W‖ ^ 2) +
          (s ^ 2 / 8) * ‖P.V t‖ ^ 2 +
          (v * s * r / 2) * ⟪U, P.V t⟫_ℝ +
          (v * s ^ 3 / 4) *
            ⟪P.X t - P.X T, P.V t⟫_ℝ
  rw [hnorm]
  ring

end Continuous

end LemniAcc
