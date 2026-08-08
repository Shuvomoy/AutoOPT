import ITEMf.Lyapunov.BlockAlgebra
import ITEMf.Lyapunov.NormIdentities

/-!
# ITEM-f Lyapunov decrement

The interior norm recursion is converted into the exact pair of shifted
interpolation gaps.  All ranges use `Fin (N-1)`, so the decrement family is
empty at horizon `N=1`.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : Nat}

namespace StronglyConvexSmoothModel

theorem shiftedGap_nonneg
    (M : StronglyConvexSmoothModel E) (xStar x y : E) :
    0 ≤ M.shiftedGap xStar x y := by
  rw [← M.transformed_interpolationGap xStar x y]
  exact (M.transformedModel xStar).interpolationGap_nonneg x y

end StronglyConvexSmoothModel

private theorem scaled_norm_difference
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (hnorm : NormIdentitiesResult M C x0 xStar hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    M.μ / (2 * (1 - M.q) * C.Upsilon) *
        (blockNormSq (W M C x0 xStar j) -
          blockNormSq (W M C x0 xStar (nextInteriorLyapIndex i))) =
      (1 / (1 - M.q)) *
          blockInner (gapBlock M C x0 xStar j) (W M C x0 xStar j) -
        (C.a (lyapNextCoeffIndex j) / (M.L * (1 - M.q))) *
          ‖M.shiftedGrad xStar
              (itemfIterate M C x0 (j.1 + 1))‖ ^ 2 := by
  dsimp only
  let j := interiorLyapIndex i
  let Wj := W M C x0 xStar j
  let Gj := gapBlock M C x0 xStar j
  let innerWG := blockInner Gj Wj
  let g := M.shiftedGrad xStar (itemfIterate M C x0 (j.1 + 1))
  let A := C.a (lyapNextCoeffIndex j)
  have hs : sCoeff M.q C j ≠ 0 :=
    interior_s_ne_zero_of_relations M.q_unit hC hN hcoord i
  have hunit := hcoord.interior_unit i
  dsimp [j] at hunit
  have hgapNorm :
      blockNormSq Gj =
        2 * (1 - cCoeff M.q C j) * ‖g‖ ^ 2 := by
    simpa [Gj, g] using gapBlock_norm_sq M C x0 xStar j hunit
  have hrec := hnorm.interior i
  dsimp [j] at hrec
  have hrec' :
      blockNormSq (W M C x0 xStar (nextInteriorLyapIndex i)) =
        blockNormSq
          (blockSub Wj (blockScale (C.Upsilon / M.μ) Gj)) := by
    simpa [Wj, Gj, j] using hrec
  have hdiff :
      blockNormSq Wj -
          blockNormSq (W M C x0 xStar (nextInteriorLyapIndex i)) =
        2 * (C.Upsilon / M.μ) * innerWG -
          (C.Upsilon / M.μ) ^ 2 * blockNormSq Gj := by
    rw [hrec', blockNormSq_sub_scale, blockInner_comm Wj Gj]
    simp only [innerWG]
    ring
  have hc :
      1 - cCoeff M.q C j = M.q * A / C.Upsilon := by
    simp only [cCoeff, A]
    ring
  have hU0 : C.Upsilon ≠ 0 := hC.upsilon_ne_zero
  have hμ0 : M.μ ≠ 0 := ne_of_gt M.hμ
  have hL0 : M.L ≠ 0 := ne_of_gt M.hL
  have hq0 : M.q ≠ 0 := M.q_ne_zero
  have h1q0 : 1 - M.q ≠ 0 := M.one_sub_q_ne_zero
  rw [hdiff, hgapNorm, hc]
  have hqL := M.q_mul_L
  field_simp [hU0, hμ0, hL0, hq0, h1q0]
  rw [← hqL]
  ring

private theorem scaled_norm_difference_as_steps
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (hnorm : NormIdentitiesResult M C x0 xStar hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    let xk := itemfIterate M C x0 (j.1 + 1)
    let gk := M.shiftedGrad xStar xk
    M.μ / (2 * (1 - M.q) * C.Upsilon) *
        (blockNormSq (W M C x0 xStar j) -
          blockNormSq (W M C x0 xStar (nextInteriorLyapIndex i))) =
      (C.a (lyapNextCoeffIndex j) / (1 - M.q)) *
          ⟪M.gradientStep xk - xStar, gk⟫_ℝ -
        (C.a (lyapCoeffIndex j) / (1 - M.q)) *
          ⟪itemfPreviousPlus M C x0 (j.1 + 1) - xStar, gk⟫_ℝ := by
  dsimp only
  let j := interiorLyapIndex i
  let xk := itemfIterate M C x0 (j.1 + 1)
  let gk := M.shiftedGrad xStar xk
  let A := C.a (lyapNextCoeffIndex j)
  let a := C.a (lyapCoeffIndex j)
  have hs : sCoeff M.q C j ≠ 0 :=
    interior_s_ne_zero_of_relations M.q_unit hC hN hcoord i
  have hscaled :=
    scaled_norm_difference M C x0 xStar hN hC hcoord hnorm i
  dsimp only at hscaled
  rw [gapBlock_inner_W M C x0 xStar j hs] at hscaled
  have hstep := M.gradientStep_sub_eq xStar xk
  have hself : ⟪gk, gk⟫_ℝ = ‖gk‖ ^ 2 :=
    real_inner_self_eq_norm_sq gk
  have hL0 : M.L ≠ 0 := ne_of_gt M.hL
  have h1q0 : 1 - M.q ≠ 0 := M.one_sub_q_ne_zero
  have hscaled' :
      M.μ / (2 * (1 - M.q) * C.Upsilon) *
          (blockNormSq (W M C x0 xStar j) -
            blockNormSq (W M C x0 xStar (nextInteriorLyapIndex i))) =
        (1 / (1 - M.q)) *
            ⟪gk, ((1 - M.q) * A) • (xk - xStar) -
              a • (itemfPreviousPlus M C x0 (j.1 + 1) - xStar)⟫_ℝ -
          (A / (M.L * (1 - M.q))) * ‖gk‖ ^ 2 := by
    simpa [j, xk, gk, A, a] using hscaled
  have hinnerStep :
      ⟪gk, ((1 - M.q) * A) • (xk - xStar)⟫_ℝ -
          (A / M.L) * ‖gk‖ ^ 2 =
        A * ⟪gk, M.gradientStep xk - xStar⟫_ℝ := by
    rw [hstep, inner_sub_right, real_inner_smul_right,
      real_inner_smul_right]
    have hself' :
        ⟪gk, M.shiftedGrad xStar xk⟫_ℝ = ‖gk‖ ^ 2 := by
      simpa [gk] using hself
    rw [real_inner_smul_right, hself']
    field_simp [hL0]
  calc
    M.μ / (2 * (1 - M.q) * C.Upsilon) *
          (blockNormSq (W M C x0 xStar j) -
            blockNormSq (W M C x0 xStar (nextInteriorLyapIndex i))) =
        (1 / (1 - M.q)) *
            (((1 - M.q) * A) *
                ⟪gk, xk - xStar⟫_ℝ -
              (A / M.L) * ‖gk‖ ^ 2 -
              a * ⟪gk,
                itemfPreviousPlus M C x0 (j.1 + 1) - xStar⟫_ℝ) := by
      rw [hscaled']
      simp only [inner_sub_right, real_inner_smul_right]
      field_simp [hL0, h1q0]
      ring
    _ = (1 / (1 - M.q)) *
          (A * ⟪gk, M.gradientStep xk - xStar⟫_ℝ -
            a * ⟪gk,
              itemfPreviousPlus M C x0 (j.1 + 1) - xStar⟫_ℝ) := by
      rw [← hinnerStep]
      simp only [real_inner_smul_right]
    _ =
        (A / (1 - M.q)) *
            ⟪gk, M.gradientStep xk - xStar⟫_ℝ -
          (a / (1 - M.q)) *
            ⟪gk, itemfPreviousPlus M C x0 (j.1 + 1) - xStar⟫_ℝ := by
      ring
    _ = (A / (1 - M.q)) *
            ⟪M.gradientStep xk - xStar, gk⟫_ℝ -
          (a / (1 - M.q)) *
            ⟪itemfPreviousPlus M C x0 (j.1 + 1) - xStar, gk⟫_ℝ := by
      rw [real_inner_comm gk (M.gradientStep xk - xStar),
        real_inner_comm gk
          (itemfPreviousPlus M C x0 (j.1 + 1) - xStar)]

private theorem decrement_identity_of_norm
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hxStar : M.IsMinimizer xStar)
    (hN : 1 ≤ N) (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (hnorm : NormIdentitiesResult M C x0 xStar hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    potential M C x0 xStar j -
        potential M C x0 xStar (nextInteriorLyapIndex i) =
      C.a (lyapCoeffIndex j) *
          M.shiftedGap xStar
            (itemfIterate M C x0 j.1)
            (itemfIterate M C x0 (j.1 + 1)) +
        (C.a (lyapNextCoeffIndex j) -
            C.a (lyapCoeffIndex j)) *
          M.shiftedGap xStar xStar
            (itemfIterate M C x0 (j.1 + 1)) := by
  dsimp only
  let j := interiorLyapIndex i
  let xprev := itemfIterate M C x0 j.1
  let xk := itemfIterate M C x0 (j.1 + 1)
  let a := C.a (lyapCoeffIndex j)
  let A := C.a (lyapNextCoeffIndex j)
  have hidx :
      lyapCoeffIndex (nextInteriorLyapIndex i) =
        lyapNextCoeffIndex j := by
    apply Fin.ext
    simp [j, interiorLyapIndex, nextInteriorLyapIndex,
      lyapCoeffIndex, lyapNextCoeffIndex]
  have hnormStep :=
    scaled_norm_difference_as_steps M C x0 xStar hN hC hcoord hnorm i
  dsimp only at hnormStep
  have hprevPlus :
      itemfPreviousPlus M C x0 (j.1 + 1) =
        M.gradientStep xprev := by
    simpa [xprev] using itemfPreviousPlus_succ M C x0 j.1
  have hthreePrev := Internal.threePointIdentity M hxStar xprev xk
  have hthreeSelf := Internal.threePointIdentity M hxStar xk xk
  have hselfGap : M.shiftedGap xStar xk xk = 0 := by
    simp [StronglyConvexSmoothModel.shiftedGap]
  rw [hselfGap] at hthreeSelf
  rw [hprevPlus] at hnormStep
  simp only [potential]
  rw [hidx]
  dsimp [xprev, xk, a, A, j] at hnormStep hthreePrev hthreeSelf ⊢
  linear_combination
    C.a (lyapCoeffIndex (interiorLyapIndex i)) * hthreePrev -
      C.a (lyapNextCoeffIndex (interiorLyapIndex i)) * hthreeSelf +
      hnormStep

theorem lyapunovMonotone_of_normIdentities
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hxStar : M.IsMinimizer xStar)
    (hN : 1 ≤ N) (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (hnorm : NormIdentitiesResult M C x0 xStar hN) :
    LyapunovMonotoneResult M C x0 xStar := by
  have hdecrement :
      ∀ i : Fin (N - 1),
        let j := interiorLyapIndex i
        potential M C x0 xStar j -
            potential M C x0 xStar (nextInteriorLyapIndex i) =
          C.a (lyapCoeffIndex j) *
              M.shiftedGap xStar
                (itemfIterate M C x0 j.1)
                (itemfIterate M C x0 (j.1 + 1)) +
            (C.a (lyapNextCoeffIndex j) -
                C.a (lyapCoeffIndex j)) *
              M.shiftedGap xStar xStar
                (itemfIterate M C x0 (j.1 + 1)) :=
    decrement_identity_of_norm M C x0 xStar hxStar hN hC hcoord hnorm
  have hnonnegative :
      ∀ i : Fin (N - 1),
        let j := interiorLyapIndex i
        0 ≤ potential M C x0 xStar j -
          potential M C x0 xStar (nextInteriorLyapIndex i) := by
    intro i
    let j := interiorLyapIndex i
    have hd := hdecrement i
    dsimp only at hd ⊢
    rw [hd]
    have ha : 0 < C.a (lyapCoeffIndex j) := hC.a_pos _
    have horder :
        C.a (lyapCoeffIndex j) < C.a (lyapNextCoeffIndex j) :=
      hC.a_strict (by simp [lyapCoeffIndex, lyapNextCoeffIndex])
    exact add_nonneg
      (mul_nonneg ha.le
        (M.shiftedGap_nonneg xStar
          (itemfIterate M C x0 j.1)
          (itemfIterate M C x0 (j.1 + 1))))
      (mul_nonneg (sub_nonneg.mpr horder.le)
        (M.shiftedGap_nonneg xStar xStar
          (itemfIterate M C x0 (j.1 + 1))))
  refine {
    decrement := hdecrement
    nonnegative := hnonnegative
    chain := ?_
  }
  intro i j hij
  generalize hn : j.1 - i.1 = n
  induction n generalizing j with
  | zero =>
      have hval : j.1 = i.1 := by omega
      have hfin : j = i := Fin.ext hval
      subst j
      exact le_rfl
  | succ n ih =>
      have hjpos : 0 < j.1 := by omega
      let jp : Fin N := ⟨j.1 - 1, by omega⟩
      have hijp : i.1 ≤ jp.1 := by
        dsimp [jp]
        omega
      have hdiff : jp.1 - i.1 = n := by
        dsimp [jp]
        omega
      have hprior : potential M C x0 xStar jp ≤
          potential M C x0 xStar i :=
        ih hijp hdiff
      have hkRange : j.1 - 1 < N - 1 := by omega
      let k : Fin (N - 1) := ⟨j.1 - 1, hkRange⟩
      have hstep := hnonnegative k
      dsimp only at hstep
      have hindex0 : interiorLyapIndex k = jp := by
        apply Fin.ext
        rfl
      have hindex1 : nextInteriorLyapIndex k = j := by
        apply Fin.ext
        dsimp [k, nextInteriorLyapIndex]
        omega
      rw [hindex0, hindex1] at hstep
      linarith

namespace Internal

/-- Exact decrement identities and the resulting monotonicity chain for the
finite ITEM-f potential. -/
theorem lyapunovMonotone
    (N : Nat) (hN : 1 ≤ N)
    (M : StronglyConvexSmoothModel E)
    {xStar : E} (hxStar : M.IsMinimizer xStar)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 : E) :
    LyapunovMonotoneResult M C x0 xStar := by
  let hcoord :=
    ITEMf.Internal.coordinateRelations N M.q hN M.q_unit C hC
  let hnorm :=
    ITEMf.Internal.normIdentities N hN M C hC x0 xStar
  exact
    lyapunovMonotone_of_normIdentities
      M C x0 xStar hxStar hN hC hcoord hnorm

end Internal

end ITEMf
