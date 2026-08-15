import LemniAcc.Discrete.LyapunovDecrement
import LemniAcc.Discrete.Recurrence.OmegaBounds

/-!
# Discrete convergence rates for LemniAcc

This module chains the initial energy, the closed one-step decrement, and the
terminal decomposition.  The first bounds are proved for arbitrary valid
coefficient data; the public canonical bounds then use the finite
lemniscatic estimate on `omega N`.
-/

open scoped InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

namespace Discrete

/-- Exact initial energy and its immediate upper bound. -/
theorem lyapunov_initial_of_valid
    (N : Nat) {c : CoefficientData N} (v : ValidCoefficients N c)
    (M : SmoothConvexModel E) (x0 xStar : E) :
    lyapunov M N c.omega c.rho x0 xStar 0 =
        ((M.L : ℝ) / (2 * c.omega)) * ‖x0 - xStar‖ ^ 2
          - ((M.L : ℝ) / (2 * c.omega)) *
              ‖corrected M (xIterate M c.omega c.rho x0 N) - xStar‖ ^ 2
      ∧
      lyapunov M N c.omega c.rho x0 xStar 0 ≤
        ((M.L : ℝ) / (2 * c.omega)) * ‖x0 - xStar‖ ^ 2 := by
  have heq :
      lyapunov M N c.omega c.rho x0 xStar 0 =
        ((M.L : ℝ) / (2 * c.omega)) * ‖x0 - xStar‖ ^ 2
          - ((M.L : ℝ) / (2 * c.omega)) *
              ‖corrected M (xIterate M c.omega c.rho x0 N) - xStar‖ ^ 2 := by
    simp [lyapunov, previousGap, v.rho_zero, minusCoeff, terminalCoeff]
  refine ⟨heq, ?_⟩
  rw [heq]
  have hcoef :
      0 ≤ (M.L : ℝ) / (2 * c.omega) := by
    exact div_nonneg (by positivity)
      (mul_nonneg (by norm_num) v.omega_pos.le)
  have hnorm :
      0 ≤ ‖corrected M (xIterate M c.omega c.rho x0 N) - xStar‖ ^ 2 :=
    sq_nonneg _
  nlinarith [mul_nonneg hcoef hnorm]

/-- A finite chain of one-step inequalities bounds its terminal value by its
zero-th value. -/
theorem terminal_le_initial
    (V : Nat → ℝ) (N : Nat)
    (hstep : ∀ k : Nat, k < N → V (k + 1) ≤ V k) :
    V N ≤ V 0 := by
  induction N with
  | zero => exact le_rfl
  | succ n ih =>
      exact (hstep n (Nat.lt_succ_self n)).trans
        (ih (fun k hk ↦ hstep k (hk.trans (Nat.lt_succ_self n))))

/-- The valid-data Lyapunov sequence is globally nonincreasing from the
initial to the terminal index. -/
theorem lyapunov_terminal_le_initial_of_valid
    (N : Nat) {c : CoefficientData N} (v : ValidCoefficients N c)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    lyapunov M N c.omega c.rho x0 xStar N ≤
      lyapunov M N c.omega c.rho x0 xStar 0 := by
  apply terminal_le_initial
  intro k hk
  exact
    (lyapunov_decrement_of_valid N v M x0 xStar hxStar k hk).2

/-- The terminal Lyapunov value also dominates the final function-value
error. -/
theorem lyapunov_terminal_function_lower_of_valid
    (N : Nat) (hN : 1 ≤ N)
    {c : CoefficientData N} (v : ValidCoefficients N c)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    M.f (xIterate M c.omega c.rho x0 N) - M.f xStar ≤
      lyapunov M N c.omega c.rho x0 xStar N := by
  let xN := xIterate M c.omega c.rho x0 N
  have hdecomposition :=
    lyapunov_terminal_of_valid N hN v M x0 xStar hxStar
  have hgradStar : M.grad xStar = 0 :=
    M.minimizer_grad_eq_zero hxStar
  have hgap :
      gap M xN xStar =
        M.f xN - M.f xStar
          - (1 / (2 * (M.L : ℝ))) * ‖M.grad xN‖ ^ 2 := by
    unfold gap SmoothConvexModel.interpolationGap
    rw [hgradStar]
    simp
  have hΩ : 1 < c.omega := valid_omega_gt_one hN v
  have hL : 0 < (M.L : ℝ) := by exact_mod_cast M.hL
  have hmain :
      M.f xN - M.f xStar ≤
        (c.omega / (2 * (M.L : ℝ))) * ‖M.grad xN‖ ^ 2
          + gap M xN xStar := by
    rw [hgap]
    have hcoef :
        0 ≤ (c.omega - 1) / (2 * (M.L : ℝ)) := by
      positivity
    have hterm :
        0 ≤ ((c.omega - 1) / (2 * (M.L : ℝ))) *
          ‖M.grad xN‖ ^ 2 :=
      mul_nonneg hcoef (sq_nonneg _)
    calc
      M.f xN - M.f xStar ≤
          M.f xN - M.f xStar
            + ((c.omega - 1) / (2 * (M.L : ℝ))) *
                ‖M.grad xN‖ ^ 2 := le_add_of_nonneg_right hterm
      _ =
          c.omega / (2 * (M.L : ℝ)) * ‖M.grad xN‖ ^ 2
            + (M.f xN - M.f xStar
              - 1 / (2 * (M.L : ℝ)) * ‖M.grad xN‖ ^ 2) := by
            field_simp
            ring
  have hgap₂ := gap_nonneg M xStar xN
  have hgap₃ :=
    gap_nonneg M
      (xIterate M c.omega c.rho x0 (N - 1)) xN
  have hterm₂ :
      0 ≤ (1 / c.omega) * gap M xStar xN :=
    mul_nonneg (by positivity) hgap₂
  have hterm₃ :
      0 ≤ ((c.omega ^ 2 - 1) / (2 * c.omega)) *
        gap M (xIterate M c.omega c.rho x0 (N - 1)) xN :=
    mul_nonneg (div_nonneg (by nlinarith) (by positivity)) hgap₃
  rw [hdecomposition]
  dsimp [xN] at hmain hterm₂ hterm₃
  linarith

/-- The first squared-gradient estimate, before using a finite lower bound on
the recurrence parameter. -/
theorem gradient_rate_of_valid
    (N : Nat) (hN : 1 ≤ N)
    {c : CoefficientData N} (v : ValidCoefficients N c)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    ‖M.grad (xIterate M c.omega c.rho x0 N)‖ ^ 2 ≤
      ((M.L : ℝ) ^ 2 / c.omega ^ 2) * ‖x0 - xStar‖ ^ 2 := by
  have hlower :=
    lyapunov_terminal_lower_of_valid N hN v M x0 xStar hxStar
  have hmono :=
    lyapunov_terminal_le_initial_of_valid N v M x0 xStar hxStar
  have hupper := (lyapunov_initial_of_valid N v M x0 xStar).2
  have hchain :
      (c.omega / (2 * (M.L : ℝ))) *
          ‖M.grad (xIterate M c.omega c.rho x0 N)‖ ^ 2
        ≤ ((M.L : ℝ) / (2 * c.omega)) * ‖x0 - xStar‖ ^ 2 :=
    hlower.trans (hmono.trans hupper)
  have hL : 0 < (M.L : ℝ) := by exact_mod_cast M.hL
  have hΩ : 0 < c.omega := v.omega_pos
  have hfactor : 0 < 2 * (M.L : ℝ) / c.omega := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hchain hfactor.le
  calc
    ‖M.grad (xIterate M c.omega c.rho x0 N)‖ ^ 2 =
        (2 * (M.L : ℝ) / c.omega) *
          ((c.omega / (2 * (M.L : ℝ))) *
            ‖M.grad (xIterate M c.omega c.rho x0 N)‖ ^ 2) := by
          field_simp
    _ ≤
        (2 * (M.L : ℝ) / c.omega) *
          (((M.L : ℝ) / (2 * c.omega)) * ‖x0 - xStar‖ ^ 2) :=
      hscaled
    _ = ((M.L : ℝ) ^ 2 / c.omega ^ 2) *
        ‖x0 - xStar‖ ^ 2 := by
          field_simp

/-- The first function-value estimate, before using a finite lower bound on
the recurrence parameter. -/
theorem functionValue_rate_of_valid
    (N : Nat) (hN : 1 ≤ N)
    {c : CoefficientData N} (v : ValidCoefficients N c)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    M.f (xIterate M c.omega c.rho x0 N) - M.f xStar ≤
      ((M.L : ℝ) / (2 * c.omega)) * ‖x0 - xStar‖ ^ 2 := by
  exact
    (lyapunov_terminal_function_lower_of_valid N hN v M x0 xStar hxStar).trans
      ((lyapunov_terminal_le_initial_of_valid N v M x0 xStar hxStar).trans
        (lyapunov_initial_of_valid N v M x0 xStar).2)

end Discrete

namespace Internal

/-- Both manuscript squared-gradient bounds for the canonical LemniAcc
trajectory. -/
theorem gradient_rate
    (N : Nat) (hN : 1 ≤ N)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    ‖M.grad (Discrete.canonicalX N M x0 N)‖ ^ 2 ≤
        ((M.L : ℝ) ^ 2 / omega N ^ 2) * ‖x0 - xStar‖ ^ 2
      ∧
      ((M.L : ℝ) ^ 2 / omega N ^ 2) * ‖x0 - xStar‖ ^ 2 ≤
        (Lemniscatic.varpi ^ 4 * (M.L : ℝ) ^ 2 *
            ‖x0 - xStar‖ ^ 2) /
          (((N + 1 : Nat) : ℝ) ^ 4) := by
  have hfirst :
      ‖M.grad (Discrete.canonicalX N M x0 N)‖ ^ 2 ≤
        ((M.L : ℝ) ^ 2 / omega N ^ 2) * ‖x0 - xStar‖ ^ 2 := by
    have hρfun : rho N = (canonicalCoefficients N).rho := by
      funext i
      rfl
    simp only [Discrete.canonicalX]
    rw [hρfun]
    simpa [omega, rho] using
      Discrete.gradient_rate_of_valid N hN
        (canonicalCoefficients_valid N) M x0 xStar hxStar
  refine ⟨hfirst, ?_⟩
  let B : ℝ := ((N + 1 : Nat) : ℝ)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hv : 0 < Lemniscatic.varpi := Lemniscatic.varpi_pos
  have hΩ : 0 < omega N := omega_pos N
  have hlower := (Internal.omega_bounds hN).1
  change B ^ 2 / Lemniscatic.varpi ^ 2 < omega N at hlower
  have hscaled :
      B ^ 2 < omega N * Lemniscatic.varpi ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hv)).mp hlower
  have hsquare :
      B ^ 4 ≤ omega N ^ 2 * Lemniscatic.varpi ^ 4 := by
    have hsum :
        0 < B ^ 2 + omega N * Lemniscatic.varpi ^ 2 := by positivity
    have hprod :=
      mul_pos (sub_pos.mpr hscaled) hsum
    nlinarith
  have hinverse :
      1 / omega N ^ 2 ≤ Lemniscatic.varpi ^ 4 / B ^ 4 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hΩ) (by positivity : 0 < B ^ 4)]
    nlinarith
  have hnonneg :
      0 ≤ (M.L : ℝ) ^ 2 * ‖x0 - xStar‖ ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hinverse hnonneg
  dsimp [B] at hmul ⊢
  calc
    ((M.L : ℝ) ^ 2 / omega N ^ 2) * ‖x0 - xStar‖ ^ 2 =
        (1 / omega N ^ 2) *
          ((M.L : ℝ) ^ 2 * ‖x0 - xStar‖ ^ 2) := by ring
    _ ≤
        (Lemniscatic.varpi ^ 4 / (((N + 1 : Nat) : ℝ) ^ 4)) *
          ((M.L : ℝ) ^ 2 * ‖x0 - xStar‖ ^ 2) := hmul
    _ = _ := by ring

/-- Both manuscript function-value bounds for the canonical LemniAcc
trajectory. -/
theorem functionValue_rate
    (N : Nat) (hN : 1 ≤ N)
    (M : SmoothConvexModel E) (x0 xStar : E)
    (hxStar : M.IsMinimizer xStar) :
    M.f (Discrete.canonicalX N M x0 N) - M.f xStar ≤
        ((M.L : ℝ) / (2 * omega N)) * ‖x0 - xStar‖ ^ 2
      ∧
      ((M.L : ℝ) / (2 * omega N)) * ‖x0 - xStar‖ ^ 2 ≤
        (Lemniscatic.varpi ^ 2 * (M.L : ℝ) *
            ‖x0 - xStar‖ ^ 2) /
          (2 * (((N + 1 : Nat) : ℝ) ^ 2)) := by
  have hfirst :
      M.f (Discrete.canonicalX N M x0 N) - M.f xStar ≤
        ((M.L : ℝ) / (2 * omega N)) * ‖x0 - xStar‖ ^ 2 := by
    have hρfun : rho N = (canonicalCoefficients N).rho := by
      funext i
      rfl
    simp only [Discrete.canonicalX]
    rw [hρfun]
    simpa [omega, rho] using
      Discrete.functionValue_rate_of_valid N hN
        (canonicalCoefficients_valid N) M x0 xStar hxStar
  refine ⟨hfirst, ?_⟩
  let B : ℝ := ((N + 1 : Nat) : ℝ)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hv : 0 < Lemniscatic.varpi := Lemniscatic.varpi_pos
  have hΩ : 0 < omega N := omega_pos N
  have hlower := (Internal.omega_bounds hN).1
  change B ^ 2 / Lemniscatic.varpi ^ 2 < omega N at hlower
  have hscaled :
      B ^ 2 < omega N * Lemniscatic.varpi ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hv)).mp hlower
  have hinverse :
      1 / omega N ≤ Lemniscatic.varpi ^ 2 / B ^ 2 := by
    rw [div_le_div_iff₀ hΩ (sq_pos_of_pos hB)]
    nlinarith
  have hnonneg :
      0 ≤ ((M.L : ℝ) / 2) * ‖x0 - xStar‖ ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hinverse hnonneg
  dsimp [B] at hmul ⊢
  calc
    ((M.L : ℝ) / (2 * omega N)) * ‖x0 - xStar‖ ^ 2 =
        (1 / omega N) *
          (((M.L : ℝ) / 2) * ‖x0 - xStar‖ ^ 2) := by ring
    _ ≤
        (Lemniscatic.varpi ^ 2 / (((N + 1 : Nat) : ℝ) ^ 2)) *
          (((M.L : ℝ) / 2) * ‖x0 - xStar‖ ^ 2) := hmul
    _ = _ := by ring

end Internal

end LemniAcc
