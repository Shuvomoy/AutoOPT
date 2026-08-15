import LemniAcc.Spec

/-!
# Trusted LemniAcc Comparator challenge

This file fixes the ten public theorem statements and contains exactly one
approved placeholder for each statement. Its local import closure is the
proof-free `LemniAcc.Spec` tree.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

theorem finite_interpolation
    {d n : Nat}
    (M : SmoothConvexModel (Euclidean d))
    (x : Fin n → Euclidean d) :
    ∀ i j : Fin n,
      M.f (x j) + ⟪M.grad (x j), x i - x j⟫_ℝ +
          (1 / (2 * (M.L : ℝ))) *
            ‖M.grad (x i) - M.grad (x j)‖ ^ 2 ≤
        M.f (x i) := by sorry

theorem recurrence_existsUnique (N : Nat) :
    ∃! c : CoefficientData N, ValidCoefficients N c := by sorry

theorem omega_bounds
    {N : Nat} (hN : 1 ≤ N) :
    ((N + 1 : Nat) : ℝ) ^ 2 / Lemniscatic.varpi ^ 2 < omega N ∧
      omega N < ((N + 1 : Nat) : ℝ) ^ 2 := by sorry

theorem iterates
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
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
              Discrete.canonicalZ N M x0 k) := by sorry

theorem lyapunov_terminal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (N : Nat) (hN : 1 ≤ N)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    Discrete.lyapunov M N (omega N) (rho N) x0 xStar N =
      (omega N / (2 * (M.L : ℝ))) *
          ‖M.grad (Discrete.canonicalX N M x0 N)‖ ^ 2
        + Discrete.gap M (Discrete.canonicalX N M x0 N) xStar
        + (1 / omega N) *
            Discrete.gap M xStar (Discrete.canonicalX N M x0 N)
        + ((omega N ^ 2 - 1) / (2 * omega N)) *
            Discrete.gap M (Discrete.canonicalX N M x0 (N - 1))
              (Discrete.canonicalX N M x0 N) := by sorry

theorem lyapunov_decrement
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (N : Nat) (_hN : 1 ≤ N)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    ∀ k : Nat, k < N →
      (Discrete.lyapunov M N (omega N) (rho N) x0 xStar k
            - Discrete.lyapunov M N (omega N) (rho N) x0 xStar (k + 1) =
          Discrete.minusCoeff (rho N k) *
              Discrete.previousCurrentGap M (omega N) (rho N) x0 k
            + (rho N k - rho N (k + 1)) *
                Discrete.gap M xStar (Discrete.canonicalX N M x0 k)
            + (Discrete.plusCoeff (rho N (k + 1)) -
                Discrete.plusCoeff (rho N k)) *
                Discrete.gap M (Discrete.canonicalX N M x0 N)
                  (Discrete.canonicalX N M x0 k))
        ∧
        Discrete.lyapunov M N (omega N) (rho N) x0 xStar (k + 1) ≤
          Discrete.lyapunov M N (omega N) (rho N) x0 xStar k := by sorry

theorem gradient_rate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (N : Nat) (hN : 1 ≤ N)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    ‖M.grad (Discrete.canonicalX N M x0 N)‖ ^ 2 ≤
        ((M.L : ℝ) ^ 2 / omega N ^ 2) * ‖x0 - xStar‖ ^ 2
      ∧
      ((M.L : ℝ) ^ 2 / omega N ^ 2) * ‖x0 - xStar‖ ^ 2 ≤
        (Lemniscatic.varpi ^ 4 * (M.L : ℝ) ^ 2 *
            ‖x0 - xStar‖ ^ 2) /
          (((N + 1 : Nat) : ℝ) ^ 4) := by sorry

theorem functionValue_rate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (N : Nat) (hN : 1 ≤ N)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    M.f (Discrete.canonicalX N M x0 N) - M.f xStar ≤
        ((M.L : ℝ) / (2 * omega N)) * ‖x0 - xStar‖ ^ 2
      ∧
      ((M.L : ℝ) / (2 * omega N)) * ‖x0 - xStar‖ ^ 2 ≤
        (Lemniscatic.varpi ^ 2 * (M.L : ℝ) *
            ‖x0 - xStar‖ ^ 2) /
          (2 * (((N + 1 : Nat) : ℝ) ^ 2)) := by sorry

namespace Lemniscatic

theorem sigma_identities (T : ℝ) (hT : 0 < T) :
    SigmaIdentities T := by sorry

end Lemniscatic

theorem continuousTime_lyapunov
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (M : SmoothConvexModel E) (T : ℝ) (hT : 0 < T)
    (xStar : E) (hxStar : M.IsMinimizer xStar)
    (x0 : E) (P : ContinuousTrajectory M T x0) :
    ‖M.grad (P.X T)‖ ^ 2 ≤
        (Lemniscatic.varpi ^ 4 / T ^ 4) *
          ‖x0 - xStar‖ ^ 2
      ∧
      M.f (P.X T) - M.f xStar ≤
        (Lemniscatic.varpi ^ 2 / (2 * T ^ 2)) *
          ‖x0 - xStar‖ ^ 2 := by sorry

end LemniAcc
