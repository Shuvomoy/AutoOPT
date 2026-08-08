import LemniAcc.Model
import LemniAcc.Discrete.LyapunovAlgebra

/-!
# Finite LemniAcc iterates

The algorithm is represented as a recursion on the pair `(xₖ,zₖ)`.  This
module proves existence and uniqueness of the trajectory through a prescribed
finite horizon.  Positivity and recurrence properties of the scalar
coefficients are deliberately separate from this purely recursive fact.
-/

open scoped InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

namespace Discrete

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

@[simp] theorem iterateState_zero
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ) (x0 : E) :
    iterateState M Ω ρ x0 0 = (x0, 0) :=
  rfl

@[simp] theorem iterateState_succ
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 : E) (k : Nat) :
    iterateState M Ω ρ x0 (k + 1) =
      step M Ω ρ k (iterateState M Ω ρ x0 k) :=
  rfl

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

@[simp] theorem xIterate_zero
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ) (x0 : E) :
    xIterate M Ω ρ x0 0 = x0 :=
  rfl

@[simp] theorem zIterate_zero
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ) (x0 : E) :
    zIterate M Ω ρ x0 0 = 0 :=
  rfl

/-- The momentum update in component form. -/
theorem zIterate_succ
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 : E) (k : Nat) :
    zIterate M Ω ρ x0 (k + 1) =
      zIterate M Ω ρ x0 k -
        (Ω * (plusCoeff (ρ (k + 1)) - plusCoeff (ρ k)) *
          (M.L : ℝ)⁻¹) • M.grad (xIterate M Ω ρ x0 k) := by
  rfl

/-- The position update in component form. -/
theorem xIterate_succ
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 : E) (k : Nat) :
    xIterate M Ω ρ x0 (k + 1) =
      M.gradientStep (xIterate M Ω ρ x0 k) +
        (positionCoeff (ρ (k + 1)) - positionCoeff (ρ (k + 2))) •
          zIterate M Ω ρ x0 (k + 1) := by
  rfl

end Discrete

/-- For any scalar coefficient sequence, the LemniAcc updates determine a
unique trajectory through the prescribed finite horizon.  The paper-facing
`LemniAcc.iterates` theorem later combines this fact with the unique
coefficient construction. -/
theorem iterates_of_coefficients
    (N : Nat) (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 : E) :
    ∃ state : Nat → E × E,
      state 0 = (x0, 0) ∧
      (∀ k : Nat, k < N →
        state (k + 1) = Discrete.step M Ω ρ k (state k)) ∧
      ∀ other : Nat → E × E,
        other 0 = (x0, 0) →
        (∀ k : Nat, k < N →
          other (k + 1) = Discrete.step M Ω ρ k (other k)) →
        ∀ k : Nat, k ≤ N →
          other k = state k := by
  refine ⟨Discrete.iterateState M Ω ρ x0, rfl, ?_, ?_⟩
  · intro k _
    rfl
  · intro other hzero hstep k hk
    induction k with
    | zero =>
        simpa using hzero
    | succ k ih =>
        rw [hstep k (Nat.lt_of_succ_le hk), Discrete.iterateState_succ]
        rw [ih (Nat.le_trans (Nat.le_succ k) hk)]

end LemniAcc
