import LemniAcc.Spec.Basic

/-!
# Proof-free lemniscatic and continuous-coefficient declarations

The extended lemniscatic sine is a total conditional choice.  The analytic
proof layer establishes existence, uniqueness, and agreement with the inverse
order isomorphism on the clamped domain.
-/

open scoped Interval Topology
open Set MeasureTheory intervalIntegral Filter

set_option autoImplicit false

namespace LemniAcc.Lemniscatic

/-- The density in the defining integral of the lemniscatic sine. -/
noncomputable def arcslIntegrand (x : ℝ) : ℝ :=
  (Real.sqrt (1 - x ^ 4))⁻¹

/-- The inverse coordinate whose inverse on `[0,1]` is the lemniscatic sine. -/
noncomputable def arcsl (u : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..u, arcslIntegrand x

/-- The lemniscate constant. -/
noncomputable def varpi : ℝ :=
  2 * arcsl 1

/-- The comparison kernel appearing in the finite omega bound. -/
noncomputable def omegaKernel (x : ℝ) : ℝ :=
  (Real.sqrt (x * (1 - x ^ 2)))⁻¹

/-- The clamped inverse-coordinate value. -/
noncomputable def angleClampValue (x : ℝ) : ℝ :=
  min (max x 0) (varpi / 2)

/-- The lemniscatic sine, extended totally outside its defining interval. -/
noncomputable def sl (x : ℝ) : ℝ := by
  classical
  exact
    if h : ∃ u : ℝ,
        u ∈ Icc (0 : ℝ) 1 ∧ arcsl u = angleClampValue x then
      Classical.choose h
    else
      0

/-- The lemniscatic cosine as the reflected lemniscatic sine. -/
noncomputable def cl (x : ℝ) : ℝ :=
  sl (varpi / 2 - x)

/-- The horizon-scaled lemniscate constant. -/
noncomputable def varpiT (T : ℝ) : ℝ :=
  varpi / T

/-- The lemniscatic argument at time `t`. -/
noncomputable def scaledAngle (T t : ℝ) : ℝ :=
  varpi * t / (2 * T)

/-- The continuous coefficient `rho(t)`. -/
noncomputable def rho (T : ℝ) : ℝ → ℝ :=
  (cl ∘ scaledAngle T) ^ 2

/-- The continuous coefficient `sigma(t)`. -/
noncomputable def sigma (T t : ℝ) : ℝ :=
  Real.sqrt ((1 - rho T t ^ 2) / rho T t)

/-- The paper's first derivative formula for `sigma`. -/
noncomputable def sigmaDot (T t : ℝ) : ℝ :=
  varpiT T / 2 * (rho T t + (rho T t)⁻¹)

/-- The friction coefficient in the singular second-order ODE. -/
noncomputable def gamma (T t : ℝ) : ℝ :=
  3 * sigmaDot T t / sigma T t

/-- The complete lemniscatic-calculus and coefficient interface. -/
structure SigmaIdentities (T : ℝ) : Prop where
  horizon_pos : 0 < T
  sl_continuous_on_real : Continuous sl
  sl_strict_increasing :
    StrictMonoOn sl (Icc (0 : ℝ) (varpi / 2))
  sl_bijection :
    BijOn sl (Icc (0 : ℝ) (varpi / 2)) (Icc (0 : ℝ) 1)
  sl_endpoints : sl 0 = 0 ∧ sl (varpi / 2) = 1
  cl_continuous_on_real : Continuous cl
  cl_strict_decreasing :
    StrictAntiOn cl (Icc (0 : ℝ) (varpi / 2))
  cl_bijection :
    BijOn cl (Icc (0 : ℝ) (varpi / 2)) (Icc (0 : ℝ) 1)
  cl_endpoints : cl 0 = 1 ∧ cl (varpi / 2) = 0
  interior_values :
    ∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) (varpi / 2) →
      sl x ∈ Ioo (0 : ℝ) 1 ∧ cl x ∈ Ioo (0 : ℝ) 1
  sl_derivative :
    ∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) (varpi / 2) →
      HasDerivAt sl (Real.sqrt (1 - sl x ^ 4)) x
  cl_derivative :
    ∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) (varpi / 2) →
      HasDerivAt cl (-Real.sqrt (1 - cl x ^ 4)) x
  complement_identity :
    ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) (varpi / 2) →
      cl (varpi / 2 - x) = sl x
  complement_square :
    ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) (varpi / 2) →
      cl x ^ 2 = (1 - sl x ^ 2) / (1 + sl x ^ 2)
  complement_algebra :
    ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) (varpi / 2) →
      cl x ^ 2 + sl x ^ 2 + cl x ^ 2 * sl x ^ 2 = 1
  sl_first_order :
    (fun x : ℝ => sl x - x) =o[𝓝[>] (0 : ℝ)] fun x : ℝ => x
  rho_interior :
    ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) T →
      0 < rho T t ∧ rho T t < 1
  rho_symmetry :
    ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) T →
      rho T (T - t) = (1 - rho T t) / (1 + rho T t)
  rho_derivative_root :
    ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) T →
      HasDerivAt (rho T)
        (-varpiT T * Real.sqrt (rho T t * (1 - rho T t ^ 2))) t
  rho_derivative_sigma :
    ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) T →
      HasDerivAt (rho T)
        (-varpiT T * sigma T t * rho T t) t
  sigma_derivative :
    ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) T →
      HasDerivAt (sigma T) (sigmaDot T t) t
  sigma_second_derivative :
    ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) T →
      HasDerivAt (sigmaDot T)
        (varpiT T ^ 2 / 2 * sigma T t ^ 3) t
  sigma_reflection :
    ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) T →
      sigma T t * sigma T (T - t) = 2

end LemniAcc.Lemniscatic
