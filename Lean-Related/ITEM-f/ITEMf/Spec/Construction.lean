import ITEMf.Spec.Basic

/-!
# Specification of the analytic ITEM-f construction

This file contains the proof-free data and theorem contracts for the finite
geometric construction in Appendix B.1 of the manuscript.  Indices are finite:
`Fin (N + 2)` represents the manuscript indices `0, ..., N + 1`.
-/

open Set Filter

set_option autoImplicit false

namespace ITEMf

/-- The finite coefficient configuration at horizon `N`. -/
structure CoeffData (N : Nat) where
  Upsilon : ℝ
  a : Fin (N + 2) → ℝ
  b : Fin (N + 2) → ℝ

/-- Manuscript index `0`. -/
def idxZero (N : Nat) : Fin (N + 2) :=
  ⟨0, by omega⟩

/-- Manuscript index `N`. -/
def idxN (N : Nat) : Fin (N + 2) :=
  ⟨N, by omega⟩

/-- Manuscript index `N + 1`. -/
def idxLast (N : Nat) : Fin (N + 2) :=
  ⟨N + 1, by omega⟩

/-- Embed a chord index `k = 0, ..., N` into the coefficient indices. -/
def idxChordLeft {N : Nat} (k : Fin (N + 1)) : Fin (N + 2) :=
  ⟨k.1, by omega⟩

/-- Embed the right endpoint `k + 1` of a chord. -/
def idxChordRight {N : Nat} (k : Fin (N + 1)) : Fin (N + 2) :=
  ⟨k.1 + 1, by omega⟩

/-- Embed an interior circle index `k + 1 = 1, ..., N`. -/
def idxInterior {N : Nat} (k : Fin N) : Fin (N + 2) :=
  ⟨k.1 + 1, by omega⟩

/-- The reversed manuscript index `N + 1 - k`. -/
def reverseIndex {N : Nat} (k : Fin (N + 2)) : Fin (N + 2) :=
  Fin.rev k

/-- The radius `sqrt (Upsilon^2 - 1)` of a candidate circle. -/
noncomputable def radius (Upsilon : ℝ) : ℝ :=
  Real.sqrt (Upsilon ^ 2 - 1)

/-- The squared radius, kept polynomial in the geometric conditions. -/
def radiusSq (Upsilon : ℝ) : ℝ :=
  Upsilon ^ 2 - 1

/-- The exact positive, ordered circle-and-chord configuration of the
manuscript.  Only the interior points `1, ..., N` carry a separately stated
circle equation, exactly as in Lemma `lem:itemf-construction`; the two endpoint
formulas imply their own circle equations. -/
structure ValidCoefficients {N : Nat} (q : ℝ) (C : CoeffData N) : Prop where
  upsilon_gt_one : 1 < C.Upsilon
  a_strict :
    ∀ {i j : Fin (N + 2)}, i.1 < j.1 → C.a i < C.a j
  b_pos : ∀ i : Fin (N + 2), 0 < C.b i
  circle :
    ∀ k : Fin N,
      (C.a (idxInterior k) - C.Upsilon) ^ 2 +
          C.b (idxInterior k) ^ 2 =
        radiusSq C.Upsilon
  chord :
    ∀ k : Fin (N + 1),
      (C.a (idxChordLeft k) - C.Upsilon) *
            (C.a (idxChordRight k) - C.Upsilon) +
          C.b (idxChordLeft k) * C.b (idxChordRight k) =
        radiusSq C.Upsilon *
          (1 - q * C.a (idxChordRight k) / C.Upsilon)
  a_zero : C.a (idxZero N) = 1 / C.Upsilon
  b_zero :
    C.b (idxZero N) =
      Real.sqrt (1 - q) * radius C.Upsilon / C.Upsilon
  a_last : C.a (idxLast N) = C.Upsilon
  b_last :
    C.b (idxLast N) =
      Real.sqrt (1 - q) * radius C.Upsilon

/-- The arccos argument in one backward shooting step. -/
noncomputable def oneStepArg (q p theta : ℝ) : ℝ :=
  1 - q - p * Real.cos theta

/-- The backward shooting map
`theta ↦ theta + arccos (1 - q - p cos theta)`. -/
noncomputable def oneStep (q p theta : ℝ) : ℝ :=
  theta + Real.arccos (oneStepArg q p theta)

/-- The parameter `q sqrt (1 - Upsilon⁻²)` attached to a candidate circle. -/
noncomputable def candidateP (q Upsilon : ℝ) : ℝ :=
  q * Real.sqrt (1 - Upsilon⁻¹ ^ 2)

/-- The terminal angle `arccos (-sqrt q)`. -/
noncomputable def terminalAngle (q : ℝ) : ℝ :=
  Real.arccos (-Real.sqrt q)

/-- The shooting angle with manuscript index `k + 1`.

The exponent is `N - 1 - k`; thus at `k = N - 1` this is the terminal angle.
For `N = 1`, the orbit consists of the terminal angle alone.
-/
noncomputable def shootingAngle
    (N : Nat) (q Upsilon : ℝ) (k : Fin N) : ℝ :=
  (oneStep q (candidateP q Upsilon))^[N - 1 - k.1] (terminalAngle q)

/-- The first backward-orbit angle.  Natural subtraction makes this total at
`N = 0`; all construction theorems explicitly assume `1 ≤ N`. -/
noncomputable def shootingFirst (N : Nat) (q Upsilon : ℝ) : ℝ :=
  (oneStep q (candidateP q Upsilon))^[N - 1] (terminalAngle q)

/-- The cosine of the farther target intersection. -/
noncomputable def targetCos (q Upsilon : ℝ) : ℝ :=
  (Real.sqrt q -
      (1 - q) * radius Upsilon * Upsilon) /
    (q + (1 - q) * Upsilon ^ 2)

/-- The target angle of the farther intersection. -/
noncomputable def targetAngleValue (q Upsilon : ℝ) : ℝ :=
  Real.arccos (targetCos q Upsilon)

/-- The corrected derivative of `targetCos`, as ratified in AR031. -/
noncomputable def targetCosDerivative (q Upsilon : ℝ) : ℝ :=
  -((1 - q) *
      ((1 + q) * Upsilon ^ 2 - q +
        2 * Real.sqrt q * Upsilon * radius Upsilon)) /
    (radius Upsilon *
      (q + (1 - q) * Upsilon ^ 2) ^ 2)

/-- The shooting residual `theta_1(Upsilon) - vartheta(Upsilon)`. -/
noncomputable def shootingResidual (N : Nat) (q Upsilon : ℝ) : ℝ :=
  shootingFirst N q Upsilon - targetAngleValue q Upsilon

/-- Exact conclusions of the one-step lemma at a fixed admissible `q,p`. -/
structure OneStepMapResult (q p : ℝ) : Prop where
  argument_mem :
    ∀ theta : ℝ, oneStepArg q p theta ∈ Ioo (-1 : ℝ) 1
  step_mem :
    ∀ theta : ℝ, oneStep q p theta - theta ∈ Ioo (0 : ℝ) Real.pi
  angle_strictMono : StrictMono (oneStep q p)
  parameter_decreases :
    ∀ {p' theta : ℝ},
      0 < p' → p' < q → p < p' → Real.cos theta < 0 →
        oneStep q p' theta < oneStep q p theta

/-- Exact finite orbit comparison for manuscript indices `1, ..., N - 1`. -/
def OrbitComparisonResult
    (N : Nat) (q Upsilon Upsilon' : ℝ) : Prop :=
  ∀ k : Fin (N - 1),
    shootingAngle N q Upsilon' ⟨k.1, by omega⟩ <
      shootingAngle N q Upsilon ⟨k.1, by omega⟩

/-- Exact range, continuity, monotonicity, derivative, and endpoint-limit
package for the target angle. -/
structure TargetAngleResult (q : ℝ) : Prop where
  range :
    ∀ {Upsilon : ℝ}, 1 < Upsilon →
      targetAngleValue q Upsilon ∈ Ioo (0 : ℝ) Real.pi
  continuousOn :
    ContinuousOn (targetAngleValue q) (Ioi (1 : ℝ))
  strictMonoOn :
    StrictMonoOn (targetAngleValue q) (Ioi (1 : ℝ))
  targetCos_derivative :
    ∀ {Upsilon : ℝ}, 1 < Upsilon →
      HasDerivAt (targetCos q) (targetCosDerivative q Upsilon) Upsilon
  tendsto_one :
    Tendsto (targetAngleValue q) (nhdsWithin (1 : ℝ) (Ioi 1))
      (nhds (Real.arccos (Real.sqrt q)))
  tendsto_atTop :
    Tendsto (targetAngleValue q) atTop (nhds Real.pi)

/-- The manuscript's fixed-candidate shooting equivalence, including
coordinate uniqueness when the residual vanishes. -/
def ShootingIffAdmissibleResult
    (N : Nat) (q Upsilon : ℝ) : Prop :=
  (∃! C : CoeffData N,
      C.Upsilon = Upsilon ∧ ValidCoefficients q C) ↔
    shootingResidual N q Upsilon = 0

/-- Both coordinate identities supplied by reversal of the construction. -/
def InvolutionSymmetryResult
    {N : Nat} (C : CoeffData N) : Prop :=
  ∀ k : Fin (N + 2),
    C.a k * C.a (reverseIndex k) = 1 ∧
      C.a k * C.b (reverseIndex k) = C.b k

/-- The explicit rate relaxation used by the ITEM-f convergence theorem. -/
def ExplicitRateResult
    {N : Nat} (q : ℝ) (C : CoeffData N) : Prop :=
  1 / C.Upsilon ^ 2 <
    4 * (1 - Real.sqrt q) ^ (2 * N)

end ITEMf
