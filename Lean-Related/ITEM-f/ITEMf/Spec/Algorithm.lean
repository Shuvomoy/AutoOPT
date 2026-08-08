import ITEMf.Spec.Model
import ITEMf.Spec.Construction

/-!
# Two-state first-order recursions

The ITEM-f momentum formula uses the convention `x⁺₋₁ = x₀`.  Rather than
introducing negative natural-number indices, this module stores the pair
`(xₖ, x⁺ₖ₋₁)`.  The construction-specific coefficients are supplied by a
finite table in `MomentumCoefficients`.
-/

open scoped InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : Nat}

/-- The two scalar multipliers in a finite-horizon ITEM-f-style momentum
update.  The first multiplies `x⁺ₖ - x⁺ₖ₋₁`, and the second multiplies
`x⁺ₖ - xₖ`. -/
structure MomentumCoefficients (N : Nat) where
  first : Fin N → ℝ
  second : Fin N → ℝ

/-- The state `(xₖ, x⁺ₖ₋₁)` used to express the convention `x⁺₋₁ = x₀`
without an integer-indexed trajectory. -/
structure AlgorithmState (E : Type*) where
  x : E
  previousPlus : E

namespace AlgorithmState

/-- One generic two-state momentum update. -/
noncomputable def step
    (M : StronglyConvexSmoothModel E) (α β : ℝ)
    (state : AlgorithmState E) : AlgorithmState E :=
  let xPlus := M.gradientStep state.x
  {
    x := xPlus + α • (xPlus - state.previousPlus) +
      β • (xPlus - state.x)
    previousPlus := xPlus
  }

end AlgorithmState

namespace MomentumCoefficients

/-- Extend a finite coefficient table by zero outside its declared horizon.
Only indices below `N` are used when forming the horizon-`N` trajectory. -/
def firstAt (coeff : MomentumCoefficients N) (k : Nat) : ℝ :=
  if hk : k < N then coeff.first ⟨k, hk⟩ else 0

/-- Extend the second finite coefficient table by zero outside its declared
horizon. -/
def secondAt (coeff : MomentumCoefficients N) (k : Nat) : ℝ :=
  if hk : k < N then coeff.second ⟨k, hk⟩ else 0

end MomentumCoefficients

/-- The coefficient `φⱼ`, including the two endpoint definitions, for
`j = 0, ..., N`. -/
noncomputable def phi
    (q : ℝ) (C : CoeffData N) (j : Fin (N + 1)) : ℝ :=
  if j.1 = 0 then
    Real.sqrt (1 - q)
  else if j.1 = N then
    ((1 - q) * C.Upsilon + C.a (idxN N)) / Real.sqrt (1 - q)
  else
    Real.sqrt (2 * C.Upsilon * C.a (idxChordLeft j) - q)

/-- The coefficient index `N-k` occurring at algorithm step `k`. -/
def phiCurrentIndex (k : Fin N) : Fin (N + 1) :=
  ⟨N - k.1, by omega⟩

/-- The coefficient index `N-k-1` occurring at algorithm step `k`. -/
def phiPreviousIndex (k : Fin N) : Fin (N + 1) :=
  ⟨N - k.1 - 1, by omega⟩

/-- The exact two finite coefficient tables in the manuscript's ITEM-f
momentum update. -/
noncomputable def itemfMomentumCoefficients
    (q : ℝ) (C : CoeffData N) : MomentumCoefficients N where
  first k :=
    C.a (idxChordLeft (Fin.castSucc k)) * phi q C (phiPreviousIndex k) /
      ((1 - q) * C.a (idxChordRight (Fin.castSucc k)) *
        phi q C (phiCurrentIndex k))
  second k :=
    phi q C (phiPreviousIndex k) / phi q C (phiCurrentIndex k)

/-- The complete two-state trajectory.  At time zero both coordinates are
`x₀`, encoding `x⁺₋₁ = x₀`; at every successor time the second coordinate is
the preceding gradient step. -/
noncomputable def algorithmStates
    (M : StronglyConvexSmoothModel E) (coeff : MomentumCoefficients N)
    (x0 : E) : Nat → AlgorithmState E
  | 0 => { x := x0, previousPlus := x0 }
  | k + 1 =>
      (algorithmStates M coeff x0 k).step M
        (coeff.firstAt k) (coeff.secondAt k)

/-- The iterate coordinate of the two-state trajectory. -/
noncomputable def algorithmIterate
    (M : StronglyConvexSmoothModel E) (coeff : MomentumCoefficients N)
    (x0 : E) (k : Nat) : E :=
  (algorithmStates M coeff x0 k).x

/-- The stored preceding-gradient-step coordinate. -/
noncomputable def algorithmPreviousPlus
    (M : StronglyConvexSmoothModel E) (coeff : MomentumCoefficients N)
    (x0 : E) (k : Nat) : E :=
  (algorithmStates M coeff x0 k).previousPlus

/-- The manuscript ITEM-f two-state trajectory. -/
noncomputable def itemfStates
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 : E) : Nat → AlgorithmState E :=
  algorithmStates M (itemfMomentumCoefficients M.q C) x0

/-- The ITEM-f iterate `xₖ`. -/
noncomputable def itemfIterate
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 : E) (k : Nat) : E :=
  algorithmIterate M (itemfMomentumCoefficients M.q C) x0 k

/-- The stored value `x⁺ₖ₋₁` in the ITEM-f state at time `k`. -/
noncomputable def itemfPreviousPlus
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 : E) (k : Nat) : E :=
  algorithmPreviousPlus M (itemfMomentumCoefficients M.q C) x0 k

end ITEMf
