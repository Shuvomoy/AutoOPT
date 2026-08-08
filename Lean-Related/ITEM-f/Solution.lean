import ITEMf

/-!
# O011 Comparator solution

This file repeats the fourteen trusted-Challenge theorem signatures under the
required public names and discharges each statement using the completed
`ITEMf.Internal` proof closure.
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
        M.f (x i) :=
  ITEMf.Internal.finiteInterpolation M x

theorem oneStepMap
    (q p : ℝ) (hq : UnitRatio q) (hp0 : 0 < p) (hpq : p < q) :
    OneStepMapResult q p :=
  ITEMf.Internal.oneStepMap q p hq hp0 hpq

theorem orbitComparison
    (N : Nat) (q Upsilon Upsilon' : ℝ)
    (hN : 2 ≤ N) (hq : UnitRatio q)
    (hUpsilon : 1 < Upsilon) (horder : Upsilon < Upsilon')
    (hfirst : shootingFirst N q Upsilon ≤ Real.pi) :
    OrbitComparisonResult N q Upsilon Upsilon' :=
  ITEMf.Internal.orbitComparison N q Upsilon Upsilon' hN hq hUpsilon
    horder hfirst

theorem targetAngle
    (q : ℝ) (hq : UnitRatio q) :
    TargetAngleResult q :=
  ITEMf.Internal.targetAngle q hq

theorem shootingIffAdmissible
    (N : Nat) (q Upsilon : ℝ)
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    ShootingIffAdmissibleResult N q Upsilon :=
  ITEMf.Internal.shootingIffAdmissible N q Upsilon hN hq hUpsilon

theorem coefficientsExistUnique
    (N : Nat) (q : ℝ) (hN : 1 ≤ N) (hq : UnitRatio q) :
    ∃! C : CoeffData N, ValidCoefficients q C :=
  ITEMf.Internal.coefficientsExistUnique N q hN hq

theorem involutionSymmetry
    {N : Nat} {q : ℝ} (hN : 1 ≤ N) (hq : UnitRatio q)
    (C : CoeffData N) (hC : ValidCoefficients q C) :
    InvolutionSymmetryResult C :=
  ITEMf.Internal.involutionSymmetry hN hq C hC

theorem explicitRate
    {N : Nat} {q : ℝ} (hN : 1 ≤ N) (hq : UnitRatio q)
    (C : CoeffData N) (hC : ValidCoefficients q C) :
    ExplicitRateResult q C :=
  ITEMf.Internal.explicitRate hN hq C hC

theorem transformedMemF0
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) :
    ∃ T : SmoothConvexModel E,
      T.L = M.L - M.μ ∧
      (∀ x : E, T.f x = M.shiftedF xStar x) ∧
      (∀ x : E, T.grad x = M.shiftedGrad xStar x) ∧
      T.f xStar = 0 ∧ T.grad xStar = 0 :=
  ITEMf.Internal.transformedMemF0 M hxStar

theorem threePointIdentity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) (x y : E) :
    M.shiftedGap xStar x xStar -
        (1 / (1 - M.q)) *
          ⟪M.gradientStep x - xStar, M.shiftedGrad xStar y⟫_ℝ =
      M.shiftedGap xStar x y - M.shiftedGap xStar xStar y :=
  ITEMf.Internal.threePointIdentity M hxStar x y

theorem coordinateRelations
    (N : Nat) (q : ℝ) (hN : 1 ≤ N) (hq : UnitRatio q)
    (C : CoeffData N) (hC : ValidCoefficients q C) :
    CoordinateRelationsResult q C hN :=
  ITEMf.Internal.coordinateRelations N q hN hq C hC

theorem normIdentities
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : Nat) (hN : 1 ≤ N)
    (M : StronglyConvexSmoothModel E)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 xStar : E) :
    NormIdentitiesResult M C x0 xStar hN :=
  ITEMf.Internal.normIdentities N hN M C hC x0 xStar

theorem lyapunovMonotone
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : Nat) (hN : 1 ≤ N)
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 : E) :
    LyapunovMonotoneResult M C x0 xStar :=
  ITEMf.Internal.lyapunovMonotone N hN M hxStar C hC x0

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
            (M.f x0 - M.f xStar) :=
  ITEMf.Internal.convergence hd hN M hxStar C hC x0

end ITEMf

