import LemniAcc.Discrete.Gaps
import LemniAcc.Discrete.Iterates
import LemniAcc.Discrete.CanonicalIterates

/-!
# Terminal value of the discrete LemniAcc Lyapunov sequence

The definitions below encode the manuscript Lyapunov sequence without
introducing artificial negative indices.  Its first gap term is defined by an
explicit `Nat` split and is zero at `k = 0`.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

namespace Discrete

/-- Solving the last position update gives the endpoint vector identity used
in the terminal Lyapunov expansion. -/
theorem terminal_vector_identity
    (N : Nat) (hN : 1 ≤ N)
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 xStar : E)
    (hΩ : 1 < Ω)
    (hρN : ρ N = Ω⁻¹)
    (hρend : ρ (N + 1) = 0) :
    xIterate M Ω ρ x0 N - xStar + zIterate M Ω ρ x0 N =
      (-((Ω ^ 2 - 1) / 2)) •
          (corrected M (xIterate M Ω ρ x0 (N - 1)) - xStar)
        + ((Ω ^ 2 + 1) / 2) •
          (xIterate M Ω ρ x0 N - xStar) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hΩ0 : Ω ≠ 0 := ne_of_gt (lt_trans zero_lt_one hΩ)
  have hΩsq : Ω ^ 2 ≠ 1 := by nlinarith
  have hx := xIterate_succ M Ω ρ x0 n
  rw [hρN, hρend] at hx
  have hcoef :
      positionCoeff Ω⁻¹ - positionCoeff 0 =
        2 / (Ω ^ 2 - 1) := by
    unfold positionCoeff
    field_simp
    ring
  have hx' :
      xIterate M Ω ρ x0 (n + 1)
          - corrected M (xIterate M Ω ρ x0 n) =
        (2 / (Ω ^ 2 - 1)) • zIterate M Ω ρ x0 (n + 1) := by
    simpa [corrected, hcoef] using
      congrArg
        (fun v : E ↦ v - M.gradientStep (xIterate M Ω ρ x0 n)) hx
  have hprod :
      ((Ω ^ 2 - 1) / 2) * (2 / (Ω ^ 2 - 1)) = 1 := by
    field_simp
  have hz :
      zIterate M Ω ρ x0 (n + 1) =
        ((Ω ^ 2 - 1) / 2) •
          (xIterate M Ω ρ x0 (n + 1)
            - corrected M (xIterate M Ω ρ x0 n)) := by
    rw [hx', smul_smul, hprod, one_smul]
  rw [Nat.succ_sub_one, hz]
  module

/-- Expanding the difference of the two terminal squared norms leaves one
gradient inner product and one gradient-norm correction. -/
theorem terminal_energy_difference
    (M : SmoothConvexModel E) (Ω : ℝ) (x xStar z : E)
    (hΩ : Ω ≠ 0) :
    ((M.L : ℝ) / (2 * Ω)) * ‖x - xStar + z‖ ^ 2
        - ((M.L : ℝ) / (2 * Ω)) *
            ‖corrected M x - xStar + z‖ ^ 2 =
      (1 / Ω) * ⟪x - xStar + z, M.grad x⟫_ℝ
        - (1 / (2 * (M.L : ℝ) * Ω)) * ‖M.grad x‖ ^ 2 := by
  have hL : 0 < (M.L : ℝ) := by exact_mod_cast M.hL
  have hcorrected :
      corrected M x - xStar + z =
        (x - xStar + z) - ((M.L : ℝ)⁻¹) • M.grad x := by
    unfold corrected SmoothConvexModel.gradientStep
    module
  rw [hcorrected, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
  field_simp
  ring

/-- The terminal Lyapunov algebra after the two endpoint coefficient values
have been substituted.  This theorem is independent of how the valid
coefficient sequence was constructed. -/
theorem terminal_decomposition_algebra
    (M : SmoothConvexModel E) (Ω : ℝ) (xPrev x xStar z : E)
    (hxStar : M.IsMinimizer xStar) (hΩ : 1 < Ω)
    (hvector :
      x - xStar + z =
        (-((Ω ^ 2 - 1) / 2)) • (corrected M xPrev - xStar)
          + ((Ω ^ 2 + 1) / 2) • (x - xStar)) :
    ((Ω ^ 2 - 1) / (2 * Ω)) * gap M xPrev xStar
        - ((Ω - 1) ^ 2 / (2 * Ω)) * gap M x xStar
        + ((M.L : ℝ) / (2 * Ω)) * ‖x - xStar + z‖ ^ 2
        - ((M.L : ℝ) / (2 * Ω)) *
            ‖corrected M x - xStar + z‖ ^ 2 =
      (Ω / (2 * (M.L : ℝ))) * ‖M.grad x‖ ^ 2
        + gap M x xStar
        + (1 / Ω) * gap M xStar x
        + ((Ω ^ 2 - 1) / (2 * Ω)) * gap M xPrev x := by
  have hΩ0 : Ω ≠ 0 := ne_of_gt (lt_trans zero_lt_one hΩ)
  have hL : (M.L : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt M.hL
  have henergy :=
    terminal_energy_difference M Ω x xStar z hΩ0
  have hprev := gap_three_point M hxStar xPrev x
  have hcurrent := gap_three_point M hxStar x x
  simp only [gap_self, zero_sub] at hcurrent
  have hprev_inner :
      ⟪corrected M xPrev - xStar, M.grad x⟫_ℝ =
        gap M xPrev xStar - gap M xPrev x + gap M xStar x := by
    linarith
  have hcurrent_inner :
      ⟪corrected M x - xStar, M.grad x⟫_ℝ =
        gap M x xStar + gap M xStar x := by
    linarith
  have hxcorrected :
      x - xStar =
        (corrected M x - xStar) + ((M.L : ℝ)⁻¹) • M.grad x := by
    unfold corrected SmoothConvexModel.gradientStep
    module
  have hinner :
      ⟪x - xStar + z, M.grad x⟫_ℝ =
        (-((Ω ^ 2 - 1) / 2)) *
            ⟪corrected M xPrev - xStar, M.grad x⟫_ℝ
          + ((Ω ^ 2 + 1) / 2) *
            ⟪x - xStar, M.grad x⟫_ℝ := by
    rw [hvector, inner_add_left, real_inner_smul_left,
      real_inner_smul_left]
  have hinner_x :
      ⟪x - xStar, M.grad x⟫_ℝ =
        ⟪corrected M x - xStar, M.grad x⟫_ℝ
          + (M.L : ℝ)⁻¹ * ‖M.grad x‖ ^ 2 := by
    rw [hxcorrected, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  calc
    _ =
        ((Ω ^ 2 - 1) / (2 * Ω)) * gap M xPrev xStar
          - ((Ω - 1) ^ 2 / (2 * Ω)) * gap M x xStar
          + (((M.L : ℝ) / (2 * Ω)) * ‖x - xStar + z‖ ^ 2
            - ((M.L : ℝ) / (2 * Ω)) *
                ‖corrected M x - xStar + z‖ ^ 2) := by
          ring
    _ = _ := by
      rw [henergy, hinner, hinner_x, hprev_inner, hcurrent_inner]
      field_simp
      ring

/-- Exact terminal decomposition for any coefficient sequence with the
manuscript endpoint values. -/
theorem lyapunov_terminal_decomposition
    (N : Nat) (hN : 1 ≤ N)
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) (hΩ : 1 < Ω)
    (hρN : ρ N = Ω⁻¹) (hρend : ρ (N + 1) = 0) :
    lyapunov M N Ω ρ x0 xStar N =
      (Ω / (2 * (M.L : ℝ))) *
          ‖M.grad (xIterate M Ω ρ x0 N)‖ ^ 2
        + gap M (xIterate M Ω ρ x0 N) xStar
        + (1 / Ω) * gap M xStar (xIterate M Ω ρ x0 N)
        + ((Ω ^ 2 - 1) / (2 * Ω)) *
            gap M (xIterate M Ω ρ x0 (N - 1))
              (xIterate M Ω ρ x0 N) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hΩ0 : Ω ≠ 0 := ne_of_gt (lt_trans zero_lt_one hΩ)
  have hminus :
      minusCoeff Ω⁻¹ = (Ω ^ 2 - 1) / (2 * Ω) := by
    unfold minusCoeff
    field_simp
  have hterminal :
      terminalCoeff Ω⁻¹ = (Ω - 1) ^ 2 / (2 * Ω) := by
    unfold terminalCoeff
    field_simp
  have hposition : positionCoeff 0 = 1 := by
    norm_num [positionCoeff]
  have hvector :=
    terminal_vector_identity (n + 1) (by omega) M Ω ρ x0 xStar
      hΩ hρN hρend
  have hdecomposition :=
    terminal_decomposition_algebra M Ω
      (xIterate M Ω ρ x0 n) (xIterate M Ω ρ x0 (n + 1))
      xStar (zIterate M Ω ρ x0 (n + 1)) hxStar hΩ hvector
  rw [Nat.succ_sub_one]
  rw [show
      lyapunov M (n + 1) Ω ρ x0 xStar (n + 1) =
        ((Ω ^ 2 - 1) / (2 * Ω)) *
            gap M (xIterate M Ω ρ x0 n) xStar
          - ((Ω - 1) ^ 2 / (2 * Ω)) *
              gap M (xIterate M Ω ρ x0 (n + 1)) xStar
          + ((M.L : ℝ) / (2 * Ω)) *
              ‖xIterate M Ω ρ x0 (n + 1) - xStar
                + zIterate M Ω ρ x0 (n + 1)‖ ^ 2
          - ((M.L : ℝ) / (2 * Ω)) *
              ‖corrected M (xIterate M Ω ρ x0 (n + 1)) - xStar
                + zIterate M Ω ρ x0 (n + 1)‖ ^ 2 by
      simp only [lyapunov, previousGap, hρN, hρend, hminus, hterminal,
        hposition, one_smul]]
  exact hdecomposition

/-- The terminal Lyapunov value dominates the scaled squared gradient norm. -/
theorem lyapunov_terminal_lower
    (N : Nat) (hN : 1 ≤ N)
    (M : SmoothConvexModel E) (Ω : ℝ) (ρ : Nat → ℝ)
    (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) (hΩ : 1 < Ω)
    (hρN : ρ N = Ω⁻¹) (hρend : ρ (N + 1) = 0) :
    (Ω / (2 * (M.L : ℝ))) *
        ‖M.grad (xIterate M Ω ρ x0 N)‖ ^ 2
      ≤ lyapunov M N Ω ρ x0 xStar N := by
  rw [lyapunov_terminal_decomposition N hN M Ω ρ x0 xStar
    hxStar hΩ hρN hρend]
  have hΩpos : 0 < Ω := lt_trans zero_lt_one hΩ
  have hgap₁ :=
    gap_nonneg M (xIterate M Ω ρ x0 N) xStar
  have hgap₂ :=
    gap_nonneg M xStar (xIterate M Ω ρ x0 N)
  have hgap₃ :=
    gap_nonneg M (xIterate M Ω ρ x0 (N - 1))
      (xIterate M Ω ρ x0 N)
  have hterm₂ :
      0 ≤ (1 / Ω) * gap M xStar (xIterate M Ω ρ x0 N) :=
    mul_nonneg (by positivity) hgap₂
  have hterm₃ :
      0 ≤ ((Ω ^ 2 - 1) / (2 * Ω)) *
        gap M (xIterate M Ω ρ x0 (N - 1))
          (xIterate M Ω ρ x0 N) :=
    mul_nonneg
      (div_nonneg (by nlinarith) (by positivity)) hgap₃
  linarith

/-- A valid positive-horizon coefficient sequence has a recurrence parameter
strictly larger than one. -/
theorem valid_omega_gt_one
    {N : Nat} (hN : 1 ≤ N) {c : CoefficientData N}
    (v : ValidCoefficients N c) :
    1 < c.omega := by
  have hfirst : c.rho 1 < 1 := by
    have := v.rho_strict 0 (Nat.zero_le N)
    rwa [v.rho_zero] at this
  have hlast_le : c.rho N ≤ c.rho 1 :=
    v.rho_antitone hN
  have hlast_lt : c.rho N < 1 := lt_of_le_of_lt hlast_le hfirst
  have hmul_lt : c.omega * c.rho N < c.omega * 1 :=
    mul_lt_mul_of_pos_left hlast_lt v.omega_pos
  rw [v.last_product, mul_one] at hmul_lt
  exact hmul_lt

/-- The penultimate recurrence coefficient equals the reciprocal parameter. -/
theorem valid_rho_last
    {N : Nat} {c : CoefficientData N}
    (v : ValidCoefficients N c) :
    c.rho N = c.omega⁻¹ := by
  have hΩ0 : c.omega ≠ 0 := ne_of_gt v.omega_pos
  rw [← one_div]
  apply (eq_div_iff hΩ0).2
  simpa [mul_comm] using v.last_product

/-- Exact terminal decomposition for arbitrary valid positive-horizon
coefficient data. -/
theorem lyapunov_terminal_of_valid
    (N : Nat) (hN : 1 ≤ N)
    {c : CoefficientData N} (v : ValidCoefficients N c)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    lyapunov M N c.omega c.rho x0 xStar N =
      (c.omega / (2 * (M.L : ℝ))) *
          ‖M.grad (xIterate M c.omega c.rho x0 N)‖ ^ 2
        + gap M (xIterate M c.omega c.rho x0 N) xStar
        + (1 / c.omega) *
            gap M xStar (xIterate M c.omega c.rho x0 N)
        + ((c.omega ^ 2 - 1) / (2 * c.omega)) *
            gap M (xIterate M c.omega c.rho x0 (N - 1))
              (xIterate M c.omega c.rho x0 N) :=
  lyapunov_terminal_decomposition N hN M c.omega c.rho x0 xStar
    hxStar (valid_omega_gt_one hN v) (valid_rho_last v) v.rho_terminal

/-- Scaled-gradient lower bound for arbitrary valid positive-horizon
coefficient data. -/
theorem lyapunov_terminal_lower_of_valid
    (N : Nat) (hN : 1 ≤ N)
    {c : CoefficientData N} (v : ValidCoefficients N c)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    (c.omega / (2 * (M.L : ℝ))) *
        ‖M.grad (xIterate M c.omega c.rho x0 N)‖ ^ 2
      ≤ lyapunov M N c.omega c.rho x0 xStar N :=
  lyapunov_terminal_lower N hN M c.omega c.rho x0 xStar
    hxStar (valid_omega_gt_one hN v) (valid_rho_last v) v.rho_terminal

end Discrete

namespace Internal

/-- The canonical terminal Lyapunov value has the exact four-term
decomposition stated in the manuscript. -/
theorem lyapunov_terminal
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
              (Discrete.canonicalX N M x0 N) := by
  have hρfun : rho N = (canonicalCoefficients N).rho := by
    funext i
    rfl
  simp only [Discrete.canonicalX]
  rw [hρfun]
  simpa [omega, rho] using
    Discrete.lyapunov_terminal_of_valid N hN
      (canonicalCoefficients_valid N) M x0 xStar hxStar

end Internal

end LemniAcc
