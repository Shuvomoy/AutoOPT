import LemniAcc.Spec.Model
import LemniAcc.Spec.Recurrence

/-!
# Proof-free discrete LemniAcc declarations
-/

open scoped InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

namespace Discrete

/-- The coefficient `(1-r²)/(2r)` appearing in the Lyapunov sequence. -/
noncomputable def minusCoeff (r : ℝ) : ℝ :=
  (1 - r ^ 2) / (2 * r)

/-- The coefficient `(1+r²)/(2r)` appearing in the momentum update. -/
noncomputable def plusCoeff (r : ℝ) : ℝ :=
  (1 + r ^ 2) / (2 * r)

/-- The coefficient `(1+r²)/(1-r²)` appearing in the position update. -/
noncomputable def positionCoeff (r : ℝ) : ℝ :=
  (1 + r ^ 2) / (1 - r ^ 2)

/-- One step of the two-sequence form of LemniAcc. -/
noncomputable def step
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (k : Nat) (state : E × E) : E × E :=
  let x := state.1
  let z := state.2
  let zNext :=
    z -
      (Ω * (plusCoeff (ρ (k + 1)) - plusCoeff (ρ k)) *
        (M.L : ℝ)⁻¹) • M.grad x
  let xNext :=
    M.gradientStep x +
      (positionCoeff (ρ (k + 1)) - positionCoeff (ρ (k + 2))) • zNext
  (xNext, zNext)

/-- The canonical infinite recursion whose restriction gives every finite
LemniAcc trajectory. -/
noncomputable def iterateState
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 : E) : Nat → E × E
  | 0 => (x0, 0)
  | k + 1 => step M Ω ρ k (iterateState M Ω ρ x0 k)

/-- The position component of the canonical LemniAcc recursion. -/
noncomputable def xIterate
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 : E) (k : Nat) : E :=
  (iterateState M Ω ρ x0 k).1

/-- The momentum component of the canonical LemniAcc recursion. -/
noncomputable def zIterate
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 : E) (k : Nat) : E :=
  (iterateState M Ω ρ x0 k).2

/-- Position in the trajectory using the selected horizon-`N` coefficients. -/
noncomputable def canonicalX
    (N : Nat) (M : SmoothConvexModel E) (x0 : E) (k : Nat) : E :=
  xIterate M (omega N) (rho N) x0 k

/-- Momentum in the trajectory using the selected horizon-`N` coefficients. -/
noncomputable def canonicalZ
    (N : Nat) (M : SmoothConvexModel E) (x0 : E) (k : Nat) : E :=
  zIterate M (omega N) (rho N) x0 k

/-- The smooth-convex interpolation gap between two actual sample points. -/
noncomputable def gap
    (M : SmoothConvexModel E) (x y : E) : ℝ :=
  M.interpolationGap x y

/-- A reciprocal-smoothness gradient step, denoted `x⁺` in the manuscript. -/
noncomputable def corrected
    (M : SmoothConvexModel E) (x : E) : E :=
  M.gradientStep x

/-- The coefficient `(1-r)²/(2r)` of the terminal-to-minimizer gap. -/
noncomputable def terminalCoeff (r : ℝ) : ℝ :=
  (1 - r) ^ 2 / (2 * r)

/-- The manuscript term `D_{k-1,⋆}`, with its genuine zero-horizon value. -/
noncomputable def previousGap
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 xStar : E) : Nat → ℝ
  | 0 => 0
  | k + 1 => gap M (xIterate M Ω ρ x0 k) xStar

/-- The discrete Lyapunov sequence from the manuscript. -/
noncomputable def lyapunov
    (M : SmoothConvexModel E) (N : Nat) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 xStar : E) (k : Nat) : ℝ :=
  minusCoeff (ρ k) * previousGap M Ω ρ x0 xStar k
    - terminalCoeff (ρ k) * gap M (xIterate M Ω ρ x0 N) xStar
    + ((M.L : ℝ) / (2 * Ω)) *
        ‖xIterate M Ω ρ x0 k - xStar
          + positionCoeff (ρ (k + 1)) • zIterate M Ω ρ x0 k‖ ^ 2
    - ((M.L : ℝ) / (2 * Ω)) *
        ‖corrected M (xIterate M Ω ρ x0 N) - xStar
          + zIterate M Ω ρ x0 k‖ ^ 2

/-- The gap `D_{k-1,k}` for a positive index, and zero at index zero. -/
noncomputable def previousCurrentGap
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 : E) : Nat → ℝ
  | 0 => 0
  | k + 1 =>
      gap M (xIterate M Ω ρ x0 k) (xIterate M Ω ρ x0 (k + 1))

/-- The closed nonnegative-gap expression for one Lyapunov decrement. -/
noncomputable def decrementExpression
    (M : SmoothConvexModel E) (N : Nat) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 xStar : E) (k : Nat) : ℝ :=
  minusCoeff (ρ k) * previousCurrentGap M Ω ρ x0 k
    + (ρ k - ρ (k + 1)) * gap M xStar (xIterate M Ω ρ x0 k)
    + (plusCoeff (ρ (k + 1)) - plusCoeff (ρ k)) *
        gap M (xIterate M Ω ρ x0 N) (xIterate M Ω ρ x0 k)

end Discrete

end LemniAcc
