import LemniAcc.Discrete.Recurrence.ExistenceUnique
import LemniAcc.Discrete.Iterates

/-!
# Canonical LemniAcc trajectory

This module links the purely recursive two-sequence algorithm to the unique
finite-horizon coefficient data.  The resulting paper-facing theorem states
both update equations and uniqueness of the trajectory through the horizon.
-/

open scoped InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

namespace Discrete

@[simp] theorem canonicalX_zero
    (N : Nat) (M : SmoothConvexModel E) (x0 : E) :
    canonicalX N M x0 0 = x0 :=
  rfl

@[simp] theorem canonicalZ_zero
    (N : Nat) (M : SmoothConvexModel E) (x0 : E) :
    canonicalZ N M x0 0 = 0 :=
  rfl

end Discrete

namespace Internal

/-- The unique valid recurrence coefficients determine a unique LemniAcc
trajectory, initialized by `x₀` and `z₀ = 0`, that obeys both manuscript
updates through step `N - 1`. -/
theorem iterates
    (N : Nat) (_hN : 1 ≤ N)
    (M : SmoothConvexModel E) (x0 : E) :
    ValidCoefficients N (canonicalCoefficients N) ∧
      Discrete.canonicalX N M x0 0 = x0 ∧
      Discrete.canonicalZ N M x0 0 = 0 ∧
      (∀ k : Nat, k < N →
        Discrete.canonicalZ N M x0 (k + 1) =
            Discrete.canonicalZ N M x0 k -
              (omega N *
                  (Discrete.plusCoeff (rho N (k + 1)) -
                    Discrete.plusCoeff (rho N k)) *
                (M.L : ℝ)⁻¹) •
                M.grad (Discrete.canonicalX N M x0 k) ∧
          Discrete.canonicalX N M x0 (k + 1) =
            M.gradientStep (Discrete.canonicalX N M x0 k) +
              (Discrete.positionCoeff (rho N (k + 1)) -
                Discrete.positionCoeff (rho N (k + 2))) •
                Discrete.canonicalZ N M x0 (k + 1)) ∧
      ∀ other : Nat → E × E,
        other 0 = (x0, 0) →
        (∀ k : Nat, k < N →
          other (k + 1) =
            Discrete.step M (omega N) (rho N) k (other k)) →
        ∀ k : Nat, k ≤ N →
          other k =
            (Discrete.canonicalX N M x0 k,
              Discrete.canonicalZ N M x0 k) := by
  refine
    ⟨canonicalCoefficients_valid N, rfl, rfl, ?_, ?_⟩
  · intro k _
    exact
      ⟨Discrete.zIterate_succ M (omega N) (rho N) x0 k,
        Discrete.xIterate_succ M (omega N) (rho N) x0 k⟩
  · intro other hzero hstep k hk
    rcases
        iterates_of_coefficients N M (omega N) (rho N) x0 with
      ⟨state, _hstateZero, _hstateStep, hunique⟩
    have hother : other k = state k :=
      hunique other hzero hstep k hk
    have hcanonical :
        Discrete.iterateState M (omega N) (rho N) x0 k = state k :=
      hunique
        (Discrete.iterateState M (omega N) (rho N) x0)
        rfl (fun _ _ => rfl) k hk
    simpa [Discrete.canonicalX, Discrete.canonicalZ,
      Discrete.xIterate, Discrete.zIterate] using
        hother.trans hcanonical.symm

end Internal

end LemniAcc
