import ITEMf.Lyapunov.Monotonicity
import ITEMf.Construction.ExplicitRate

/-!
# ITEM-f convergence

This file proves the two endpoint estimates for the finite Lyapunov sequence,
chains them through monotonicity, and applies the explicit construction rate.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : Nat}

private theorem shiftedGrad_at_minimizer
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) :
    M.shiftedGrad xStar xStar = 0 := by
  rw [StronglyConvexSmoothModel.shiftedGrad,
    M.minimizer_grad_eq_zero hxStar]
  simp

private theorem shiftedGap_self
    (M : StronglyConvexSmoothModel E) (xStar x : E) :
    M.shiftedGap xStar x x = 0 := by
  simp [StronglyConvexSmoothModel.shiftedGap]

private theorem shiftedGap_to_minimizer
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) (x : E) :
    M.shiftedGap xStar x xStar =
      M.f x - M.f xStar -
        (M.μ / 2) * ‖x - xStar‖ ^ 2 -
        (1 / (2 * (M.L - M.μ))) *
          ‖M.shiftedGrad xStar x‖ ^ 2 := by
  have hgStar := shiftedGrad_at_minimizer M hxStar
  unfold StronglyConvexSmoothModel.shiftedGap
    StronglyConvexSmoothModel.shiftedF
  rw [hgStar]
  simp

private theorem shiftedGap_from_minimizer
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar) (x : E) :
    M.shiftedGap xStar xStar x =
      -(M.f x - M.f xStar) +
        (M.μ / 2) * ‖x - xStar‖ ^ 2 +
        ⟪x - xStar, M.shiftedGrad xStar x⟫_ℝ -
        (1 / (2 * (M.L - M.μ))) *
          ‖M.shiftedGrad xStar x‖ ^ 2 := by
  have hgStar := shiftedGrad_at_minimizer M hxStar
  unfold StronglyConvexSmoothModel.shiftedGap
    StronglyConvexSmoothModel.shiftedF
  rw [hgStar]
  simp only [sub_self, norm_zero, pow_two, zero_mul, zero_sub, norm_neg]
  rw [show xStar - x = -(x - xStar) by abel]
  simp only [inner_neg_right]
  rw [real_inner_comm (M.shiftedGrad xStar x) (x - xStar)]
  ring

private theorem initial_endpoint_identity
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 : E) (hN : 1 ≤ N)
    (hnorm : NormIdentitiesResult M C x0 xStar hN) :
    (M.f x0 - M.f xStar) / C.Upsilon -
        potential M C x0 xStar (firstLyapIndex hN) =
      (C.a (lyapCoeffIndex (firstLyapIndex hN)) -
          C.a (idxZero N)) *
        M.shiftedGap xStar xStar x0 := by
  let k := firstLyapIndex hN
  let a0 := C.a (idxZero N)
  let a1 := C.a (lyapCoeffIndex k)
  let G0 := M.shiftedGap xStar x0 xStar
  let GStar0 := M.shiftedGap xStar xStar x0
  let inner0 :=
    ⟪M.gradientStep x0 - xStar, M.shiftedGrad xStar x0⟫_ℝ
  let g0 := M.shiftedGrad xStar x0
  have hnorm0 := hnorm.initial
  have hgap0 := shiftedGap_to_minimizer M hxStar x0
  have hthree := Internal.threePointIdentity M hxStar x0 x0
  have hself : M.shiftedGap xStar x0 x0 = 0 :=
    shiftedGap_self M xStar x0
  rw [hself] at hthree
  simp only [zero_sub] at hthree
  have hLm :
      M.L - M.μ = (1 - M.q) * M.L :=
    M.one_sub_q_mul_L.symm
  change
    G0 =
      M.f x0 - M.f xStar -
        M.μ / 2 * ‖x0 - xStar‖ ^ 2 -
        1 / (2 * (M.L - M.μ)) * ‖g0‖ ^ 2 at hgap0
  have hfgap :
      M.f x0 - M.f xStar =
        G0 + M.μ / 2 * ‖x0 - xStar‖ ^ 2 +
          1 / (2 * ((1 - M.q) * M.L)) * ‖g0‖ ^ 2 := by
    rw [hgap0, hLm]
    ring
  have hU0 : C.Upsilon ≠ 0 := hC.upsilon_ne_zero
  have hL0 : M.L ≠ 0 := ne_of_gt M.hL
  have hq0 : M.q ≠ 0 := M.q_ne_zero
  have h1q0 : 1 - M.q ≠ 0 := M.one_sub_q_ne_zero
  have ha0 : a0 = 1 / C.Upsilon := hC.a_zero
  change
    (M.f x0 - M.f xStar) / C.Upsilon -
        (a1 * G0 +
          M.μ / (2 * (1 - M.q) * C.Upsilon) *
            blockNormSq (W M C x0 xStar k)) =
      (a1 - a0) * GStar0
  change
    blockNormSq (W M C x0 xStar k) =
      (1 - M.q) * ‖x0 - xStar‖ ^ 2 -
        (2 * C.Upsilon / M.μ) * (a1 - a0) * inner0 +
        (C.Upsilon * a0 / (M.μ * M.L)) * ‖g0‖ ^ 2 at hnorm0
  change
    G0 - 1 / (1 - M.q) * inner0 = -GStar0 at hthree
  have hthree' :
      1 / (1 - M.q) * inner0 - G0 = GStar0 := by
    linarith
  calc
    (M.f x0 - M.f xStar) / C.Upsilon -
          (a1 * G0 +
            M.μ / (2 * (1 - M.q) * C.Upsilon) *
              blockNormSq (W M C x0 xStar k)) =
        (a1 - a0) *
          (1 / (1 - M.q) * inner0 - G0) := by
            rw [hnorm0, hfgap, ha0, ← M.q_mul_L]
            field_simp [hU0, hL0, hq0, h1q0]
            ring
    _ = (a1 - a0) * GStar0 := by rw [hthree']

private theorem initial_endpoint_bound
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 : E) (hN : 1 ≤ N)
    (hnorm : NormIdentitiesResult M C x0 xStar hN) :
    potential M C x0 xStar (firstLyapIndex hN) ≤
      (M.f x0 - M.f xStar) / C.Upsilon := by
  have hid :=
    initial_endpoint_identity M hxStar C hC x0 hN hnorm
  have ha :
      0 ≤ C.a (lyapCoeffIndex (firstLyapIndex hN)) -
        C.a (idxZero N) := by
    exact sub_nonneg.mpr
      ((hC.a_strict
        (show (idxZero N).1 <
            (lyapCoeffIndex (firstLyapIndex hN)).1 by simp)).le)
  have hgap :=
    M.shiftedGap_nonneg xStar xStar x0
  nlinarith [mul_nonneg ha hgap]

private theorem terminal_endpoint_identity
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 : E) (hN : 1 ≤ N)
    (hnorm : NormIdentitiesResult M C x0 xStar hN) :
    let xN := itemfIterate M C x0 N
    let xPrev := itemfIterate M C x0 (N - 1)
    let previousPlus := itemfPreviousPlus M C x0 N
    let gN := M.shiftedGrad xStar xN
    let residual :=
      ((1 - M.q) * C.Upsilon) • (xN - xStar) -
        C.a (idxN N) • (previousPlus - xStar)
    potential M C x0 xStar (terminalLyapIndex hN) -
          C.Upsilon * (M.f xN - M.f xStar) -
          (M.L / (2 * (1 - M.q) * C.Upsilon)) *
            ‖residual - (C.Upsilon * M.L⁻¹) • gN‖ ^ 2 =
      C.a (idxN N) * M.shiftedGap xStar xPrev xN +
        (C.Upsilon - C.a (idxN N)) *
          M.shiftedGap xStar xStar xN := by
  dsimp only
  let t := terminalLyapIndex hN
  let xN := itemfIterate M C x0 N
  let xPrev := itemfIterate M C x0 (N - 1)
  let previousPlus := itemfPreviousPlus M C x0 N
  let gN := M.shiftedGrad xStar xN
  let aN := C.a (idxN N)
  let GPrevStar := M.shiftedGap xStar xPrev xStar
  let GPrevN := M.shiftedGap xStar xPrev xN
  let GStarN := M.shiftedGap xStar xStar xN
  let innerPrev := ⟪previousPlus - xStar, gN⟫_ℝ
  let innerN := ⟪xN - xStar, gN⟫_ℝ
  let residual :=
    ((1 - M.q) * C.Upsilon) • (xN - xStar) -
      aN • (previousPlus - xStar)
  have ht : t.1 = N - 1 := rfl
  have hak : lyapCoeffIndex t = idxN N :=
    lyapCoeffIndex_terminal hN
  have hsucc : N - 1 + 1 = N := by omega
  have hpreviousPlus :
      previousPlus = M.gradientStep xPrev := by
    have htime :
        itemfPreviousPlus M C x0 (N - 1 + 1) =
          itemfPreviousPlus M C x0 N :=
      congrArg (itemfPreviousPlus M C x0) hsucc
    calc
      previousPlus =
          itemfPreviousPlus M C x0 (N - 1 + 1) := by
            exact htime.symm
      _ = M.gradientStep xPrev := by
            exact itemfPreviousPlus_succ M C x0 (N - 1)
  have hnormN := hnorm.terminal
  have hthree := Internal.threePointIdentity M hxStar xPrev xN
  rw [← hpreviousPlus] at hthree
  have hgapStar := shiftedGap_from_minimizer M hxStar xN
  have hLm :
      M.L - M.μ = (1 - M.q) * M.L :=
    M.one_sub_q_mul_L.symm
  change
    GStarN =
      -(M.f xN - M.f xStar) +
        M.μ / 2 * ‖xN - xStar‖ ^ 2 +
        innerN -
        1 / (2 * (M.L - M.μ)) * ‖gN‖ ^ 2 at hgapStar
  have hfgap :
      M.f xN - M.f xStar =
        -GStarN + M.μ / 2 * ‖xN - xStar‖ ^ 2 +
          innerN -
          1 / (2 * ((1 - M.q) * M.L)) * ‖gN‖ ^ 2 := by
    rw [hgapStar, hLm]
    ring
  have hsquare :
      ‖residual - (C.Upsilon * M.L⁻¹) • gN‖ ^ 2 =
        ‖residual‖ ^ 2 -
          2 * (C.Upsilon * M.L⁻¹) *
            ⟪residual, gN⟫_ℝ +
          (C.Upsilon * M.L⁻¹) ^ 2 * ‖gN‖ ^ 2 := by
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      real_inner_smul_right, mul_pow, sq_abs]
    ring
  have hinner :
      ⟪residual, gN⟫_ℝ =
        (1 - M.q) * C.Upsilon * innerN -
          aN * innerPrev := by
    dsimp [residual, innerN, innerPrev]
    simp only [inner_sub_left, real_inner_smul_left]
  change
    blockNormSq (W M C x0 xStar t) =
      (1 - M.q) * C.Upsilon ^ 2 * ‖xN - xStar‖ ^ 2 +
        1 / M.q * ‖residual‖ ^ 2 at hnormN
  change
    GPrevStar - 1 / (1 - M.q) * innerPrev =
      GPrevN - GStarN at hthree
  have hU0 : C.Upsilon ≠ 0 := hC.upsilon_ne_zero
  have hL0 : M.L ≠ 0 := ne_of_gt M.hL
  have hq0 : M.q ≠ 0 := M.q_ne_zero
  have h1q0 : 1 - M.q ≠ 0 := M.one_sub_q_ne_zero
  simp only [potential]
  rw [lyapCoeffIndex_terminal hN, terminalLyapIndex_val]
  change
    aN * GPrevStar +
          M.μ / (2 * (1 - M.q) * C.Upsilon) *
            blockNormSq (W M C x0 xStar t) -
        C.Upsilon * (M.f xN - M.f xStar) -
        M.L / (2 * (1 - M.q) * C.Upsilon) *
          ‖residual - (C.Upsilon * M.L⁻¹) • gN‖ ^ 2 =
      aN * GPrevN + (C.Upsilon - aN) * GStarN
  calc
    aN * GPrevStar +
            M.μ / (2 * (1 - M.q) * C.Upsilon) *
              blockNormSq (W M C x0 xStar t) -
          C.Upsilon * (M.f xN - M.f xStar) -
          M.L / (2 * (1 - M.q) * C.Upsilon) *
            ‖residual - (C.Upsilon * M.L⁻¹) • gN‖ ^ 2 =
        aN *
          (GPrevStar - 1 / (1 - M.q) * innerPrev) +
          C.Upsilon * GStarN := by
            rw [hnormN, hfgap, hsquare, hinner, ← M.q_mul_L]
            field_simp [hU0, hL0, hq0, h1q0]
            ring
    _ = aN * GPrevN + (C.Upsilon - aN) * GStarN := by
      rw [hthree]
      ring

private theorem terminal_endpoint_bound
    (M : StronglyConvexSmoothModel E) {xStar : E}
    (hxStar : M.IsMinimizer xStar)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 : E) (hN : 1 ≤ N)
    (hnorm : NormIdentitiesResult M C x0 xStar hN) :
    C.Upsilon *
        (M.f (itemfIterate M C x0 N) - M.f xStar) ≤
      potential M C x0 xStar (terminalLyapIndex hN) := by
  let xN := itemfIterate M C x0 N
  let xPrev := itemfIterate M C x0 (N - 1)
  let previousPlus := itemfPreviousPlus M C x0 N
  let gN := M.shiftedGrad xStar xN
  let aN := C.a (idxN N)
  let residual :=
    ((1 - M.q) * C.Upsilon) • (xN - xStar) -
      aN • (previousPlus - xStar)
  have hid :=
    terminal_endpoint_identity M hxStar C hC x0 hN hnorm
  dsimp only at hid
  have haN : 0 ≤ aN := by
    exact (hC.a_pos (idxN N)).le
  have haNU : 0 ≤ C.Upsilon - aN := by
    apply sub_nonneg.mpr
    apply le_of_lt
    dsimp [aN]
    rw [← hC.a_last]
    exact hC.a_strict (by simp [idxN, idxLast])
  have hgapPrev :
      0 ≤ M.shiftedGap xStar xPrev xN :=
    M.shiftedGap_nonneg xStar xPrev xN
  have hgapStar :
      0 ≤ M.shiftedGap xStar xStar xN :=
    M.shiftedGap_nonneg xStar xStar xN
  have hrhs :
      0 ≤ aN * M.shiftedGap xStar xPrev xN +
        (C.Upsilon - aN) *
          M.shiftedGap xStar xStar xN :=
    add_nonneg (mul_nonneg haN hgapPrev)
      (mul_nonneg haNU hgapStar)
  have hcoef :
      0 ≤ M.L / (2 * (1 - M.q) * C.Upsilon) := by
    have hden :
        0 < 2 * (1 - M.q) * C.Upsilon :=
      mul_pos (mul_pos (by norm_num) M.one_sub_q_pos)
        hC.upsilon_pos
    exact (div_pos M.hL hden).le
  have hsquare :
      0 ≤ ‖residual - (C.Upsilon * M.L⁻¹) • gN‖ ^ 2 :=
    sq_nonneg _
  change
    C.Upsilon * (M.f xN - M.f xStar) ≤
      potential M C x0 xStar (terminalLyapIndex hN)
  nlinarith [mul_nonneg hcoef hsquare]

namespace Internal

/-- The exact ITEM-f estimate and its explicit geometric relaxation. -/
theorem convergence
    {d N : Nat} (hd : 1 ≤ d) (hN : 1 ≤ N)
    (M : StronglyConvexSmoothModel (Euclidean d))
    {xStar : Euclidean d} (hxStar : M.IsMinimizer xStar)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 : Euclidean d) :
    M.f (itemfIterate M C x0 N) - M.f xStar ≤
          (1 / C.Upsilon ^ 2) * (M.f x0 - M.f xStar) ∧
      (1 / C.Upsilon ^ 2) * (M.f x0 - M.f xStar) ≤
          4 * (1 - Real.sqrt M.q) ^ (2 * N) *
            (M.f x0 - M.f xStar) := by
  let hnorm :=
    ITEMf.Internal.normIdentities N hN M C hC x0 xStar
  let hmono :=
    ITEMf.Internal.lyapunovMonotone N hN M hxStar C hC x0
  have hinitial :=
    initial_endpoint_bound M hxStar C hC x0 hN hnorm
  have hterminal :=
    terminal_endpoint_bound M hxStar C hC x0 hN hnorm
  have hindex :
      (firstLyapIndex hN).1 ≤ (terminalLyapIndex hN).1 := by
    change 0 ≤ N - 1
    omega
  have hchain :
      potential M C x0 xStar (terminalLyapIndex hN) ≤
        potential M C x0 xStar (firstLyapIndex hN) :=
    hmono.chain hindex
  have hraw :
      C.Upsilon *
          (M.f (itemfIterate M C x0 N) - M.f xStar) ≤
        (M.f x0 - M.f xStar) / C.Upsilon :=
    hterminal.trans (hchain.trans hinitial)
  have hU : 0 < C.Upsilon := hC.upsilon_pos
  have hscaled :=
    mul_le_mul_of_nonneg_left hraw hU.le
  have hquad :
      C.Upsilon ^ 2 *
          (M.f (itemfIterate M C x0 N) - M.f xStar) ≤
        M.f x0 - M.f xStar := by
    calc
      C.Upsilon ^ 2 *
            (M.f (itemfIterate M C x0 N) - M.f xStar) =
          C.Upsilon *
            (C.Upsilon *
              (M.f (itemfIterate M C x0 N) - M.f xStar)) := by ring
      _ ≤ C.Upsilon *
            ((M.f x0 - M.f xStar) / C.Upsilon) := hscaled
      _ = M.f x0 - M.f xStar := by
        field_simp [ne_of_gt hU]
  have hfirst :
      M.f (itemfIterate M C x0 N) - M.f xStar ≤
        (1 / C.Upsilon ^ 2) *
          (M.f x0 - M.f xStar) := by
    have hdiv :
        M.f (itemfIterate M C x0 N) - M.f xStar ≤
          (M.f x0 - M.f xStar) / C.Upsilon ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hU)).2
      simpa [mul_comm] using hquad
    calc
      M.f (itemfIterate M C x0 N) - M.f xStar ≤
          (M.f x0 - M.f xStar) / C.Upsilon ^ 2 := hdiv
      _ = (1 / C.Upsilon ^ 2) *
          (M.f x0 - M.f xStar) := by ring
  have hrate :=
    ITEMf.Internal.explicitRate hN M.q_unit C hC
  have hgap0 :
      0 ≤ M.f x0 - M.f xStar :=
    sub_nonneg.mpr (hxStar x0)
  constructor
  · exact hfirst
  · exact mul_le_mul_of_nonneg_right hrate.le hgap0

end Internal

end ITEMf
