import LemniAcc.Spec.Basic

/-!
# Proof-free recurrence declarations

The canonical coefficient selector is total.  Its proof layer later shows
that the existence branch always applies and that the selected data are the
unique valid coefficients.
-/

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

/-- The total one-step shooting map. -/
noncomputable def oneStep (Ω r : ℝ) : ℝ :=
  max 0 (oneStepRaw Ω r)

/-- Coefficient data, extended by zero after the finite horizon. -/
structure CoefficientData (N : Nat) where
  omega : ℝ
  rho : Nat → ℝ

/-- The exact finite recurrence and its endpoint/order conditions. -/
structure ValidCoefficients (N : Nat) (c : CoefficientData N) : Prop where
  omega_pos : 0 < c.omega
  rho_zero : c.rho 0 = 1
  rho_terminal : c.rho (N + 1) = 0
  rho_nonneg : ∀ k, k ≤ N + 1 → 0 ≤ c.rho k
  rho_strict : ∀ k, k ≤ N → c.rho (k + 1) < c.rho k
  recurrence : ∀ k, k ≤ N →
    OneStepRel c.omega (c.rho k) (c.rho (k + 1))
  rho_tail : ∀ k, N + 1 ≤ k → c.rho k = 0

/-- Explicit fallback used only when the validity predicate has no witness. -/
def fallbackCoefficients (N : Nat) : CoefficientData N where
  omega := 0
  rho := fun _ ↦ 0

/-- A total selector for the canonical horizon-dependent coefficients. -/
noncomputable def canonicalCoefficients (N : Nat) : CoefficientData N := by
  classical
  exact
    if h : ∃ c : CoefficientData N, ValidCoefficients N c then
      Classical.choose h
    else
      fallbackCoefficients N

/-- The selected recurrence parameter at horizon `N`. -/
noncomputable def omega (N : Nat) : ℝ :=
  (canonicalCoefficients N).omega

/-- The selected recurrence sequence at horizon `N`, extended by zero. -/
noncomputable def rho (N k : Nat) : ℝ :=
  (canonicalCoefficients N).rho k

end LemniAcc
