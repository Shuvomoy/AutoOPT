import LemniAcc.Discrete.LyapunovTerminal
import LemniAcc.Discrete.CanonicalIterates

/-!
# One-step decrement of the discrete LemniAcc Lyapunov sequence

The decrement proof is split into algebra and trajectory layers.  The
zero-th decrement is represented separately: no point or interpolation gap
with a negative index is introduced.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

namespace Discrete

/-- The gap `D_{k-1,k}` for a positive index, and the genuine value zero for
the zero-th decrement. -/
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

/-- Difference of the two quadratic energy pairs under affine gradient
updates. -/
theorem two_energy_difference
    (M : SmoothConvexModel E) (Ω a b : ℝ)
    (A ANext B BNext g : E) (hΩ : Ω ≠ 0)
    (hA : ANext =
      A - (Ω * a * (M.L : ℝ)⁻¹) • g)
    (hB : BNext =
      B - (Ω * b * (M.L : ℝ)⁻¹) • g) :
    (((M.L : ℝ) / (2 * Ω)) * ‖A‖ ^ 2
        - ((M.L : ℝ) / (2 * Ω)) * ‖B‖ ^ 2)
        - (((M.L : ℝ) / (2 * Ω)) * ‖ANext‖ ^ 2
          - ((M.L : ℝ) / (2 * Ω)) * ‖BNext‖ ^ 2) =
      a * ⟪A, g⟫_ℝ - b * ⟪B, g⟫_ℝ
        - (Ω / (2 * (M.L : ℝ))) * (a ^ 2 - b ^ 2) * ‖g‖ ^ 2 := by
  have hL : 0 < (M.L : ℝ) := by exact_mod_cast M.hL
  rw [hA, hB, norm_sub_sq_real, norm_sub_sq_real,
    real_inner_smul_right, real_inner_smul_right,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs]
  field_simp
  ring

/-- Algebraic decrement identity.  The hypotheses `hA`, `hB`, and `hdirect`
are exactly the two one-step vector relations and the direct vector identity
from the manuscript. -/
theorem decrement_algebra
    (M : SmoothConvexModel E) (Ω r s t : ℝ)
    (xPrev x xNext xN xStar z zNext : E)
    (hxStar : M.IsMinimizer xStar)
    (hΩ : Ω ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrec : Ω * (r - s) ^ 2 = r * (1 - s ^ 2))
    (hA :
      xNext - xStar + positionCoeff t • zNext =
        x - xStar + positionCoeff s • z
          - (Ω * (minusCoeff s - minusCoeff r) *
              (M.L : ℝ)⁻¹) • M.grad x)
    (hB :
      corrected M xN - xStar + zNext =
        corrected M xN - xStar + z
          - (Ω * (plusCoeff s - plusCoeff r) *
              (M.L : ℝ)⁻¹) • M.grad x)
    (hdirect :
      (minusCoeff s - minusCoeff r) •
            (x - xStar + positionCoeff s • z)
          - (plusCoeff s - plusCoeff r) •
            (corrected M xN - xStar + z) =
        (-minusCoeff r) • (corrected M xPrev - xStar)
          + minusCoeff s • (x - xStar)
          - (plusCoeff s - plusCoeff r) •
              (corrected M xN - xStar)) :
    (minusCoeff r * gap M xPrev xStar
        - terminalCoeff r * gap M xN xStar
        + ((M.L : ℝ) / (2 * Ω)) *
            ‖x - xStar + positionCoeff s • z‖ ^ 2
        - ((M.L : ℝ) / (2 * Ω)) *
            ‖corrected M xN - xStar + z‖ ^ 2)
      - (minusCoeff s * gap M x xStar
        - terminalCoeff s * gap M xN xStar
        + ((M.L : ℝ) / (2 * Ω)) *
            ‖xNext - xStar + positionCoeff t • zNext‖ ^ 2
        - ((M.L : ℝ) / (2 * Ω)) *
            ‖corrected M xN - xStar + zNext‖ ^ 2) =
      minusCoeff r * gap M xPrev x
        + (r - s) * gap M xStar x
        + (plusCoeff s - plusCoeff r) * gap M xN x := by
  let a := minusCoeff s - minusCoeff r
  let b := plusCoeff s - plusCoeff r
  have henergy :=
    two_energy_difference M Ω a b
      (x - xStar + positionCoeff s • z)
      (xNext - xStar + positionCoeff t • zNext)
      (corrected M xN - xStar + z)
      (corrected M xN - xStar + zNext)
      (M.grad x) hΩ hA hB
  have hscalar :=
    recurrence_scalar_identity_two hr hs hrec
  have hquadratic :
      (Ω / (2 * (M.L : ℝ))) * (a ^ 2 - b ^ 2) =
        minusCoeff s / (M.L : ℝ) := by
    dsimp [a, b]
    calc
      _ = (M.L : ℝ)⁻¹ *
          ((Ω / 2) *
            ((minusCoeff s - minusCoeff r) ^ 2
              - (plusCoeff s - plusCoeff r) ^ 2)) := by ring
      _ = _ := by rw [hscalar]; ring
  have hterminal :
      terminalCoeff s - terminalCoeff r =
        plusCoeff s - plusCoeff r := by
    unfold terminalCoeff plusCoeff
    field_simp
    ring
  have hinner :
      (minusCoeff s - minusCoeff r) *
            ⟪x - xStar + positionCoeff s • z, M.grad x⟫_ℝ
          - (plusCoeff s - plusCoeff r) *
            ⟪corrected M xN - xStar + z, M.grad x⟫_ℝ =
        -minusCoeff r *
            ⟪corrected M xPrev - xStar, M.grad x⟫_ℝ
          + minusCoeff s * ⟪x - xStar, M.grad x⟫_ℝ
          - (plusCoeff s - plusCoeff r) *
              ⟪corrected M xN - xStar, M.grad x⟫_ℝ := by
    calc
      _ = ⟪
          (minusCoeff s - minusCoeff r) •
              (x - xStar + positionCoeff s • z)
            - (plusCoeff s - plusCoeff r) •
              (corrected M xN - xStar + z),
          M.grad x⟫_ℝ := by
            rw [inner_sub_left, real_inner_smul_left,
              real_inner_smul_left]
      _ = ⟪
          (-minusCoeff r) • (corrected M xPrev - xStar)
            + minusCoeff s • (x - xStar)
            - (plusCoeff s - plusCoeff r) •
                (corrected M xN - xStar),
          M.grad x⟫_ℝ := by rw [hdirect]
      _ = _ := by
        rw [inner_sub_left, inner_add_left, real_inner_smul_left,
          real_inner_smul_left, real_inner_smul_left]
  have hprev := gap_three_point M hxStar xPrev x
  have hcurrent := gap_three_point M hxStar x x
  have hterminalGap := gap_three_point M hxStar xN x
  simp only [gap_self, zero_sub] at hcurrent
  have hL : (M.L : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt M.hL
  have hxcorrected :
      x - xStar =
        (corrected M x - xStar) + ((M.L : ℝ)⁻¹) • M.grad x := by
    unfold corrected SmoothConvexModel.gradientStep
    module
  have hinner_x :
      ⟪x - xStar, M.grad x⟫_ℝ =
        ⟪corrected M x - xStar, M.grad x⟫_ℝ
          + (M.L : ℝ)⁻¹ * ‖M.grad x‖ ^ 2 := by
    rw [hxcorrected, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  have hprev_inner :
      ⟪corrected M xPrev - xStar, M.grad x⟫_ℝ =
        gap M xPrev xStar - gap M xPrev x + gap M xStar x := by
    linarith
  have hcurrent_inner :
      ⟪corrected M x - xStar, M.grad x⟫_ℝ =
        gap M x xStar + gap M xStar x := by
    linarith
  have hterminal_inner :
      ⟪corrected M xN - xStar, M.grad x⟫_ℝ =
        gap M xN xStar - gap M xN x + gap M xStar x := by
    linarith
  have hcoefficient :
      minusCoeff s - minusCoeff r
          - (plusCoeff s - plusCoeff r) =
        r - s := by
    unfold minusCoeff plusCoeff
    field_simp
    ring
  calc
    _ =
        minusCoeff r * gap M xPrev xStar
          - minusCoeff s * gap M x xStar
          + (terminalCoeff s - terminalCoeff r) * gap M xN xStar
          + ((((M.L : ℝ) / (2 * Ω)) *
                ‖x - xStar + positionCoeff s • z‖ ^ 2
              - ((M.L : ℝ) / (2 * Ω)) *
                ‖corrected M xN - xStar + z‖ ^ 2)
            - (((M.L : ℝ) / (2 * Ω)) *
                ‖xNext - xStar + positionCoeff t • zNext‖ ^ 2
              - ((M.L : ℝ) / (2 * Ω)) *
                ‖corrected M xN - xStar + zNext‖ ^ 2)) := by
          ring
    _ = _ := by
      rw [henergy, hterminal, hquadratic]
      dsimp [a, b] at hinner ⊢
      rw [hinner, hinner_x, hprev_inner, hcurrent_inner,
        hterminal_inner]
      calc
        _ =
            minusCoeff r * gap M xPrev x
              + (minusCoeff s - minusCoeff r
                  - (plusCoeff s - plusCoeff r)) *
                  gap M xStar x
              + (plusCoeff s - plusCoeff r) * gap M xN x := by
                ring
        _ = _ := by rw [hcoefficient]

/-- The two affine vector updates used in the energy expansion. -/
theorem one_step_vector_identities
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 xStar xN : E) (k : Nat)
    (hr : ρ k ≠ 0) (hs : ρ (k + 1) ≠ 0)
    (hsq : (ρ (k + 1)) ^ 2 ≠ 1)
    (hrec : OneStepRel Ω (ρ k) (ρ (k + 1))) :
    (xIterate M Ω ρ x0 (k + 1) - xStar
          + positionCoeff (ρ (k + 2)) •
              zIterate M Ω ρ x0 (k + 1) =
        xIterate M Ω ρ x0 k - xStar
          + positionCoeff (ρ (k + 1)) • zIterate M Ω ρ x0 k
          - (Ω *
              (minusCoeff (ρ (k + 1)) - minusCoeff (ρ k)) *
              (M.L : ℝ)⁻¹) •
              M.grad (xIterate M Ω ρ x0 k))
      ∧
      (corrected M xN - xStar + zIterate M Ω ρ x0 (k + 1) =
        corrected M xN - xStar + zIterate M Ω ρ x0 k
          - (Ω *
              (plusCoeff (ρ (k + 1)) - plusCoeff (ρ k)) *
              (M.L : ℝ)⁻¹) •
              M.grad (xIterate M Ω ρ x0 k)) := by
  have hrec' :
      Ω * (ρ k - ρ (k + 1)) ^ 2 =
        ρ k * (1 - (ρ (k + 1)) ^ 2) := hrec
  have hscalar :=
    recurrence_scalar_identity_one hr hs hsq hrec'
  have hcoef :
      (M.L : ℝ)⁻¹
          + positionCoeff (ρ (k + 1)) *
              (Ω * (plusCoeff (ρ (k + 1)) - plusCoeff (ρ k)) *
                (M.L : ℝ)⁻¹) =
        Ω * (minusCoeff (ρ (k + 1)) - minusCoeff (ρ k)) *
          (M.L : ℝ)⁻¹ := by
    calc
      _ = (M.L : ℝ)⁻¹ *
          (Ω * (plusCoeff (ρ (k + 1)) - plusCoeff (ρ k)) *
              positionCoeff (ρ (k + 1)) + 1) := by ring
      _ = _ := by rw [hscalar]; ring
  constructor
  · rw [xIterate_succ, zIterate_succ]
    unfold SmoothConvexModel.gradientStep
    rw [← hcoef]
    module
  · rw [zIterate_succ]
    module

/-- The direct vector identity at `k = 0`; its putative previous-point
coefficient is exactly zero, and no previous gap is introduced. -/
theorem direct_vector_identity_zero
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 xStar xN : E) (hρ0 : ρ 0 = 1) :
    (minusCoeff (ρ 1) - minusCoeff (ρ 0)) •
          (xIterate M Ω ρ x0 0 - xStar
            + positionCoeff (ρ 1) • zIterate M Ω ρ x0 0)
        - (plusCoeff (ρ 1) - plusCoeff (ρ 0)) •
          (corrected M xN - xStar + zIterate M Ω ρ x0 0) =
      (-minusCoeff (ρ 0)) •
          (corrected M (xIterate M Ω ρ x0 0) - xStar)
        + minusCoeff (ρ 1) •
          (xIterate M Ω ρ x0 0 - xStar)
        - (plusCoeff (ρ 1) - plusCoeff (ρ 0)) •
          (corrected M xN - xStar) := by
  simp [hρ0, minusCoeff, plusCoeff]

/-- The direct vector identity at a strictly positive index. -/
theorem direct_vector_identity_succ
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 xStar xN : E) (j : Nat)
    (hr : ρ (j + 1) ≠ 0) (hs : ρ (j + 2) ≠ 0)
    (hrsq : (ρ (j + 1)) ^ 2 ≠ 1)
    (hssq : (ρ (j + 2)) ^ 2 ≠ 1) :
    (minusCoeff (ρ (j + 2)) - minusCoeff (ρ (j + 1))) •
          (xIterate M Ω ρ x0 (j + 1) - xStar
            + positionCoeff (ρ (j + 2)) •
                zIterate M Ω ρ x0 (j + 1))
        - (plusCoeff (ρ (j + 2)) - plusCoeff (ρ (j + 1))) •
          (corrected M xN - xStar + zIterate M Ω ρ x0 (j + 1)) =
      (-minusCoeff (ρ (j + 1))) •
          (corrected M (xIterate M Ω ρ x0 j) - xStar)
        + minusCoeff (ρ (j + 2)) •
          (xIterate M Ω ρ x0 (j + 1) - xStar)
        - (plusCoeff (ρ (j + 2)) - plusCoeff (ρ (j + 1))) •
          (corrected M xN - xStar) := by
  have hcoefficient :
      (minusCoeff (ρ (j + 2)) - minusCoeff (ρ (j + 1))) *
            positionCoeff (ρ (j + 2))
          - (plusCoeff (ρ (j + 2)) - plusCoeff (ρ (j + 1))) =
        minusCoeff (ρ (j + 1)) *
          (positionCoeff (ρ (j + 1)) -
            positionCoeff (ρ (j + 2))) := by
    unfold minusCoeff plusCoeff positionCoeff
    field_simp
    ring
  have hx :
      xIterate M Ω ρ x0 (j + 1) =
        corrected M (xIterate M Ω ρ x0 j)
          + (positionCoeff (ρ (j + 1)) -
              positionCoeff (ρ (j + 2))) •
              zIterate M Ω ρ x0 (j + 1) := by
    simpa [corrected] using xIterate_succ M Ω ρ x0 j
  have hxdiff :
      xIterate M Ω ρ x0 (j + 1)
          - corrected M (xIterate M Ω ρ x0 j) =
        (positionCoeff (ρ (j + 1)) -
          positionCoeff (ρ (j + 2))) •
            zIterate M Ω ρ x0 (j + 1) := by
    rw [hx]
    module
  calc
    _ =
        (minusCoeff (ρ (j + 2)) - minusCoeff (ρ (j + 1))) •
            (xIterate M Ω ρ x0 (j + 1) - xStar)
          + (((minusCoeff (ρ (j + 2)) - minusCoeff (ρ (j + 1))) *
                positionCoeff (ρ (j + 2))
              - (plusCoeff (ρ (j + 2)) - plusCoeff (ρ (j + 1)))) •
              zIterate M Ω ρ x0 (j + 1))
          - (plusCoeff (ρ (j + 2)) - plusCoeff (ρ (j + 1))) •
              (corrected M xN - xStar) := by
            module
    _ =
        (minusCoeff (ρ (j + 2)) - minusCoeff (ρ (j + 1))) •
            (xIterate M Ω ρ x0 (j + 1) - xStar)
          + (minusCoeff (ρ (j + 1)) *
              (positionCoeff (ρ (j + 1)) -
                positionCoeff (ρ (j + 2)))) •
              zIterate M Ω ρ x0 (j + 1)
          - (plusCoeff (ρ (j + 2)) - plusCoeff (ρ (j + 1))) •
              (corrected M xN - xStar) := by
            rw [hcoefficient]
    _ =
        (minusCoeff (ρ (j + 2)) - minusCoeff (ρ (j + 1))) •
            (xIterate M Ω ρ x0 (j + 1) - xStar)
          + minusCoeff (ρ (j + 1)) •
              (xIterate M Ω ρ x0 (j + 1)
                - corrected M (xIterate M Ω ρ x0 j))
          - (plusCoeff (ρ (j + 2)) - plusCoeff (ρ (j + 1))) •
              (corrected M xN - xStar) := by
            rw [hxdiff, smul_smul]
    _ = _ := by module

/-- Exact closed decrement for arbitrary valid coefficient data.  The proof
splits at `k = 0`, so `previousCurrentGap` never denotes a negative-index
interpolation gap. -/
theorem lyapunov_decrement_eq_of_valid
    (N : Nat) {c : CoefficientData N} (v : ValidCoefficients N c)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar)
    (k : Nat) (hk : k < N) :
    lyapunov M N c.omega c.rho x0 xStar k
        - lyapunov M N c.omega c.rho x0 xStar (k + 1) =
      decrementExpression M N c.omega c.rho x0 xStar k := by
  have hkN : k ≤ N := hk.le
  have hsuccN : k + 1 ≤ N := by omega
  have hr : c.rho k ≠ 0 := ne_of_gt (v.rho_pos hkN)
  have hs : c.rho (k + 1) ≠ 0 := ne_of_gt (v.rho_pos hsuccN)
  have hslt : c.rho (k + 1) < 1 :=
    lt_of_lt_of_le (v.rho_strict k hkN) (v.rho_le_one k)
  have hssq : (c.rho (k + 1)) ^ 2 ≠ 1 := by
    have hspos := v.rho_pos hsuccN
    nlinarith
  have hrec := v.recurrence k hkN
  rcases one_step_vector_identities M c.omega c.rho x0 xStar
      (xIterate M c.omega c.rho x0 N) k hr hs hssq hrec with
    ⟨hA, hB⟩
  cases k with
  | zero =>
      have hdirect :=
        direct_vector_identity_zero M c.omega c.rho x0 xStar
          (xIterate M c.omega c.rho x0 N) v.rho_zero
      have hdecrement :=
        decrement_algebra M c.omega (c.rho 0) (c.rho 1) (c.rho 2)
          (xIterate M c.omega c.rho x0 0)
          (xIterate M c.omega c.rho x0 0)
          (xIterate M c.omega c.rho x0 1)
          (xIterate M c.omega c.rho x0 N) xStar
          (zIterate M c.omega c.rho x0 0)
          (zIterate M c.omega c.rho x0 1)
          hxStar (ne_of_gt v.omega_pos) hr hs hrec hA hB hdirect
      simpa [lyapunov, previousGap, decrementExpression,
        previousCurrentGap, v.rho_zero, minusCoeff] using hdecrement
  | succ j =>
      have hjN : j ≤ N := by omega
      have hrlt : c.rho (j + 1) < 1 :=
        lt_of_lt_of_le (v.rho_strict j hjN) (v.rho_le_one j)
      have hrsq : (c.rho (j + 1)) ^ 2 ≠ 1 := by
        have hrpos := v.rho_pos (by omega : j + 1 ≤ N)
        nlinarith
      have hdirect :=
        direct_vector_identity_succ M c.omega c.rho x0 xStar
          (xIterate M c.omega c.rho x0 N) j hr hs hrsq hssq
      have hdecrement :=
        decrement_algebra M c.omega
          (c.rho (j + 1)) (c.rho (j + 2)) (c.rho (j + 3))
          (xIterate M c.omega c.rho x0 j)
          (xIterate M c.omega c.rho x0 (j + 1))
          (xIterate M c.omega c.rho x0 (j + 2))
          (xIterate M c.omega c.rho x0 N) xStar
          (zIterate M c.omega c.rho x0 (j + 1))
          (zIterate M c.omega c.rho x0 (j + 2))
          hxStar (ne_of_gt v.omega_pos) hr hs hrec hA hB hdirect
      simpa [lyapunov, previousGap, decrementExpression,
        previousCurrentGap] using hdecrement

/-- The closed gap expression is nonnegative for valid coefficients. -/
theorem decrementExpression_nonneg_of_valid
    (N : Nat) {c : CoefficientData N} (v : ValidCoefficients N c)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (k : Nat) (hk : k < N) :
    0 ≤ decrementExpression M N c.omega c.rho x0 xStar k := by
  have hkN : k ≤ N := hk.le
  have hsuccN : k + 1 ≤ N := by omega
  have hrpos : 0 < c.rho k := v.rho_pos hkN
  have hspos : 0 < c.rho (k + 1) := v.rho_pos hsuccN
  have hstrict : c.rho (k + 1) < c.rho k :=
    v.rho_strict k hkN
  have hrle : c.rho k ≤ 1 := v.rho_le_one k
  have hminus : 0 ≤ minusCoeff (c.rho k) := by
    unfold minusCoeff
    exact div_nonneg (by nlinarith) (by positivity)
  have hplus :
      0 ≤ plusCoeff (c.rho (k + 1)) - plusCoeff (c.rho k) :=
    sub_nonneg.mpr (plusCoeff_lt_plusCoeff hspos hstrict hrle).le
  have hprevious :
      0 ≤ previousCurrentGap M c.omega c.rho x0 k := by
    cases k with
    | zero => simp [previousCurrentGap]
    | succ j =>
        exact gap_nonneg M
          (xIterate M c.omega c.rho x0 j)
          (xIterate M c.omega c.rho x0 (j + 1))
  have hterm₁ :
      0 ≤ minusCoeff (c.rho k) *
        previousCurrentGap M c.omega c.rho x0 k :=
    mul_nonneg hminus hprevious
  have hterm₂ :
      0 ≤ (c.rho k - c.rho (k + 1)) *
        gap M xStar (xIterate M c.omega c.rho x0 k) :=
    mul_nonneg (sub_nonneg.mpr hstrict.le)
      (gap_nonneg M xStar (xIterate M c.omega c.rho x0 k))
  have hterm₃ :
      0 ≤ (plusCoeff (c.rho (k + 1)) - plusCoeff (c.rho k)) *
        gap M (xIterate M c.omega c.rho x0 N)
          (xIterate M c.omega c.rho x0 k) :=
    mul_nonneg hplus
      (gap_nonneg M (xIterate M c.omega c.rho x0 N)
        (xIterate M c.omega c.rho x0 k))
  unfold decrementExpression
  linarith

/-- Exact decrement and one-step monotonicity for arbitrary valid coefficient
data. -/
theorem lyapunov_decrement_of_valid
    (N : Nat) {c : CoefficientData N} (v : ValidCoefficients N c)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar)
    (k : Nat) (hk : k < N) :
    lyapunov M N c.omega c.rho x0 xStar k
          - lyapunov M N c.omega c.rho x0 xStar (k + 1) =
        decrementExpression M N c.omega c.rho x0 xStar k
      ∧
      lyapunov M N c.omega c.rho x0 xStar (k + 1) ≤
        lyapunov M N c.omega c.rho x0 xStar k := by
  have heq :=
    lyapunov_decrement_eq_of_valid N v M x0 xStar hxStar k hk
  have hnonneg :=
    decrementExpression_nonneg_of_valid N v M x0 xStar k hk
  exact ⟨heq, by linarith⟩

end Discrete

/-- The canonical LemniAcc Lyapunov sequence has the manuscript closed
decrement, including its explicit zero-horizon branch, and is nonincreasing
at every step before the terminal index. -/
theorem lyapunov_decrement
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
          Discrete.lyapunov M N (omega N) (rho N) x0 xStar k := by
  intro k hk
  have hρfun : rho N = (canonicalCoefficients N).rho := by
    funext i
    rfl
  simp only [Discrete.canonicalX]
  rw [hρfun]
  simpa [Discrete.decrementExpression, omega, rho] using
    Discrete.lyapunov_decrement_of_valid N
      (canonicalCoefficients_valid N) M x0 xStar hxStar k hk

end LemniAcc
