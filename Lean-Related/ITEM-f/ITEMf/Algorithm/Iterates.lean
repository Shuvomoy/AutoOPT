import ITEMf.Spec.Algorithm

/-!
# ITEM-f two-state recursion identities

The proof-bearing reduction rules for the algorithm live outside the
proof-free `Spec` closure used by `Challenge.lean`.
-/

open scoped InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : Nat}

namespace AlgorithmState

@[simp] theorem step_x
    (M : StronglyConvexSmoothModel E) (α β : ℝ)
    (state : AlgorithmState E) :
    (state.step M α β).x =
      M.gradientStep state.x +
        α • (M.gradientStep state.x - state.previousPlus) +
        β • (M.gradientStep state.x - state.x) := by
  rfl

@[simp] theorem step_previousPlus
    (M : StronglyConvexSmoothModel E) (α β : ℝ)
    (state : AlgorithmState E) :
    (state.step M α β).previousPlus = M.gradientStep state.x := by
  rfl

end AlgorithmState

namespace MomentumCoefficients

@[simp] theorem firstAt_fin (coeff : MomentumCoefficients N) (k : Fin N) :
    coeff.firstAt k = coeff.first k := by
  simp [firstAt, k.isLt]

@[simp] theorem secondAt_fin (coeff : MomentumCoefficients N) (k : Fin N) :
    coeff.secondAt k = coeff.second k := by
  simp [secondAt, k.isLt]

end MomentumCoefficients

@[simp] theorem algorithmIterate_zero
    (M : StronglyConvexSmoothModel E) (coeff : MomentumCoefficients N)
    (x0 : E) :
    algorithmIterate M coeff x0 0 = x0 := by
  rfl

@[simp] theorem algorithmPreviousPlus_zero
    (M : StronglyConvexSmoothModel E) (coeff : MomentumCoefficients N)
    (x0 : E) :
    algorithmPreviousPlus M coeff x0 0 = x0 := by
  rfl

theorem algorithmIterate_succ
    (M : StronglyConvexSmoothModel E) (coeff : MomentumCoefficients N)
    (x0 : E) (k : Nat) :
    algorithmIterate M coeff x0 (k + 1) =
      M.gradientStep (algorithmIterate M coeff x0 k) +
        coeff.firstAt k •
          (M.gradientStep (algorithmIterate M coeff x0 k) -
            algorithmPreviousPlus M coeff x0 k) +
        coeff.secondAt k •
          (M.gradientStep (algorithmIterate M coeff x0 k) -
            algorithmIterate M coeff x0 k) := by
  rfl

@[simp] theorem algorithmPreviousPlus_succ
    (M : StronglyConvexSmoothModel E) (coeff : MomentumCoefficients N)
    (x0 : E) (k : Nat) :
    algorithmPreviousPlus M coeff x0 (k + 1) =
      M.gradientStep (algorithmIterate M coeff x0 k) := by
  rfl

@[simp] theorem itemfIterate_zero
    (M : StronglyConvexSmoothModel E) (C : CoeffData N) (x0 : E) :
    itemfIterate M C x0 0 = x0 := by
  rfl

@[simp] theorem itemfPreviousPlus_zero
    (M : StronglyConvexSmoothModel E) (C : CoeffData N) (x0 : E) :
    itemfPreviousPlus M C x0 0 = x0 := by
  rfl

theorem itemfIterate_succ
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 : E) (k : Fin N) :
    itemfIterate M C x0 (k.1 + 1) =
      M.gradientStep (itemfIterate M C x0 k.1) +
        (itemfMomentumCoefficients M.q C).first k •
          (M.gradientStep (itemfIterate M C x0 k.1) -
            itemfPreviousPlus M C x0 k.1) +
        (itemfMomentumCoefficients M.q C).second k •
          (M.gradientStep (itemfIterate M C x0 k.1) -
            itemfIterate M C x0 k.1) := by
  simpa [itemfIterate, itemfPreviousPlus] using
    algorithmIterate_succ M (itemfMomentumCoefficients M.q C) x0 k.1

@[simp] theorem itemfPreviousPlus_succ
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 : E) (k : Nat) :
    itemfPreviousPlus M C x0 (k + 1) =
      M.gradientStep (itemfIterate M C x0 k) := by
  rfl

end ITEMf
