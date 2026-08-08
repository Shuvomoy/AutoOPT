import ITEMf.Spec

/-!
# Trusted O011 Comparator challenge

This file contains the fourteen theorem-facing ITEM-f statements and exactly
one approved placeholder for each statement.  Its local import closure is the
proof-free `ITEMf.Spec` tree.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

theorem finiteInterpolation
    {d n : Nat}
    (M : SmoothConvexModel (Euclidean d))
    (x : Fin n → Euclidean d) :
    ∀ i j : Fin n,
      M.f (x j) + ⟪M.grad (x j), x i - x j⟫_ℝ +
          (1 / (2 * M.L)) *
            ‖M.grad (x i) - M.grad (x j)‖ ^ 2 ≤
        M.f (x i) := by sorry

theorem oneStepMap
    (q p : ℝ) (hq : UnitRatio q) (hp0 : 0 < p) (hpq : p < q) :
    OneStepMapResult q p := by sorry

theorem orbitComparison
    (N : Nat) (q Upsilon Upsilon' : ℝ)
    (hN : 2 ≤ N) (hq : UnitRatio q)
    (hUpsilon : 1 < Upsilon) (horder : Upsilon < Upsilon')
    (hfirst : shootingFirst N q Upsilon ≤ Real.pi) :
    OrbitComparisonResult N q Upsilon Upsilon' := by sorry

theorem targetAngle
    (q : ℝ) (hq : UnitRatio q) :
    TargetAngleResult q := by sorry

theorem shootingIffAdmissible
    (N : Nat) (q Upsilon : ℝ)
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    ShootingIffAdmissibleResult N q Upsilon := by sorry

theorem coefficientsExistUnique
    (N : Nat) (q : ℝ) (hN : 1 ≤ N) (hq : UnitRatio q) :
    ∃! C : CoeffData N, ValidCoefficients q C := by sorry

theorem involutionSymmetry
    {N : Nat} {q : ℝ} (hN : 1 ≤ N) (hq : UnitRatio q)
    (C : CoeffData N) (hC : ValidCoefficients q C) :
    InvolutionSymmetryResult C := by sorry

theorem explicitRate
    {N : Nat} {q : ℝ} (hN : 1 ≤ N) (hq : UnitRatio q)
    (C : CoeffData N) (hC : ValidCoefficients q C) :
    ExplicitRateResult q C := by sorry

theorem transformedMemF0
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) :
    ∃ T : SmoothConvexModel E,
      T.L = M.L - M.μ ∧
      (∀ x : E, T.f x = M.shiftedF xStar x) ∧
      (∀ x : E, T.grad x = M.shiftedGrad xStar x) ∧
      T.f xStar = 0 ∧ T.grad xStar = 0 := by sorry

theorem threePointIdentity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) (x y : E) :
    M.shiftedGap xStar x xStar -
        (1 / (1 - M.q)) *
          ⟪M.gradientStep x - xStar, M.shiftedGrad xStar y⟫_ℝ =
      M.shiftedGap xStar x y - M.shiftedGap xStar xStar y := by sorry

theorem coordinateRelations
    (N : Nat) (q : ℝ) (hN : 1 ≤ N) (hq : UnitRatio q)
    (C : CoeffData N) (hC : ValidCoefficients q C) :
    CoordinateRelationsResult q C hN := by sorry

theorem normIdentities
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : Nat) (hN : 1 ≤ N)
    (M : StronglyConvexSmoothModel E)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 xStar : E) :
    NormIdentitiesResult M C x0 xStar hN := by sorry

theorem lyapunovMonotone
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : Nat) (hN : 1 ≤ N)
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 : E) :
    LyapunovMonotoneResult M C x0 xStar := by sorry

theorem convergence
    {d N : Nat} (hd : 1 ≤ d) (hN : 1 ≤ N)
    (M : StronglyConvexSmoothModel (Euclidean d)) {xStar : Euclidean d}
    (hxStar : M.IsMinimizer xStar)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 : Euclidean d) :
    M.f (itemfIterate M C x0 N) - M.f xStar ≤
          (1 / C.Upsilon ^ 2) * (M.f x0 - M.f xStar) ∧
      (1 / C.Upsilon ^ 2) * (M.f x0 - M.f xStar) ≤
          4 * (1 - Real.sqrt M.q) ^ (2 * N) *
            (M.f x0 - M.f xStar) := by sorry

end ITEMf
