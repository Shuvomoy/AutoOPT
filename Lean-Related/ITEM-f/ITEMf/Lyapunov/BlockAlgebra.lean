import ITEMf.Spec.Lyapunov

/-!
# Two-block inner-product algebra

These lemmas make explicit that the manuscript norm on `R^{2d}` is the sum
of the two squared block norms.  They are independent of the ITEM-f
coefficient construction.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem blockNormSq_nonneg (z : E × E) :
    0 ≤ blockNormSq z := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem blockNormSq_scale (r : ℝ) (z : E × E) :
    blockNormSq (blockScale r z) = r ^ 2 * blockNormSq z := by
  simp only [blockNormSq, blockScale, norm_smul, Real.norm_eq_abs]
  simp only [mul_pow, sq_abs]
  ring

theorem blockNormSq_sub (z w : E × E) :
    blockNormSq (blockSub z w) =
      blockNormSq z + blockNormSq w - 2 * blockInner z w := by
  simp only [blockNormSq, blockSub, blockInner, norm_sub_sq_real]
  ring

theorem blockInner_scale_right (z w : E × E) (r : ℝ) :
    blockInner z (blockScale r w) = r * blockInner z w := by
  simp only [blockInner, blockScale, real_inner_smul_right]
  ring

theorem blockInner_comm (z w : E × E) :
    blockInner z w = blockInner w z := by
  simp only [blockInner]
  rw [real_inner_comm z.1 w.1, real_inner_comm z.2 w.2]

theorem blockNormSq_sub_scale (z w : E × E) (r : ℝ) :
    blockNormSq (blockSub z (blockScale r w)) =
      blockNormSq z + r ^ 2 * blockNormSq w -
        2 * r * blockInner z w := by
  rw [blockNormSq_sub, blockNormSq_scale, blockInner_scale_right]
  ring

theorem blockRotate_norm_sq
    {c s : ℝ} (hunit : s ^ 2 + c ^ 2 = 1) (z : E × E) :
    blockNormSq (blockRotate c s z) = blockNormSq z := by
  simp only [blockNormSq, blockRotate, norm_add_sq_real, norm_smul,
    Real.norm_eq_abs, real_inner_smul_left,
    real_inner_smul_right]
  simp only [mul_pow, sq_abs, abs_neg]
  have hunit' : c ^ 2 + s ^ 2 = 1 := by linarith
  calc
    c ^ 2 * ‖z.1‖ ^ 2 + 2 * (s * (c * ⟪z.1, z.2⟫_ℝ)) +
          s ^ 2 * ‖z.2‖ ^ 2 +
        (s ^ 2 * ‖z.1‖ ^ 2 +
          2 * (c * (-s * ⟪z.1, z.2⟫_ℝ)) +
          c ^ 2 * ‖z.2‖ ^ 2) =
        (c ^ 2 + s ^ 2) * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) := by ring
    _ = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by rw [hunit']; ring

theorem blockRotate_sub_scale
    (c s r : ℝ) (z w : E × E) :
    blockRotate c s (blockSub z (blockScale r w)) =
      blockSub (blockRotate c s z)
        (blockScale r (blockRotate c s w)) := by
  apply Prod.ext <;>
    simp only [blockRotate, blockSub, blockScale, Prod.fst, Prod.snd] <;>
    module

theorem gapBlock_norm_sq
    {N : Nat}
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (i : Fin N)
    (hunit : sCoeff M.q C i ^ 2 + cCoeff M.q C i ^ 2 = 1) :
    blockNormSq (gapBlock M C x0 xStar i) =
      2 * (1 - cCoeff M.q C i) *
        ‖M.shiftedGrad xStar (itemfIterate M C x0 (i.1 + 1))‖ ^ 2 := by
  let c := cCoeff M.q C i
  let s := sCoeff M.q C i
  let g := M.shiftedGrad xStar (itemfIterate M C x0 (i.1 + 1))
  change ‖(c - 1) • g‖ ^ 2 + ‖s • g‖ ^ 2 =
    2 * (1 - c) * ‖g‖ ^ 2
  simp only [norm_smul, Real.norm_eq_abs]
  simp only [mul_pow, sq_abs]
  dsimp [c, s] at hunit ⊢
  nlinarith

theorem gapBlock_inner_W
    {N : Nat}
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (i : Fin N)
    (hs : sCoeff M.q C i ≠ 0) :
    blockInner (gapBlock M C x0 xStar i) (W M C x0 xStar i) =
      ⟪M.shiftedGrad xStar (itemfIterate M C x0 (i.1 + 1)),
        ((1 - M.q) * C.a (lyapNextCoeffIndex i)) •
            (itemfIterate M C x0 (i.1 + 1) - xStar) -
          C.a (lyapCoeffIndex i) •
            (itemfPreviousPlus M C x0 (i.1 + 1) - xStar)⟫_ℝ := by
  let c := cCoeff M.q C i
  let s := sCoeff M.q C i
  let a := C.a (lyapCoeffIndex i)
  let A := C.a (lyapNextCoeffIndex i)
  let u := itemfPreviousPlus M C x0 (i.1 + 1) - xStar
  let x := itemfIterate M C x0 (i.1 + 1) - xStar
  let g := M.shiftedGrad xStar (itemfIterate M C x0 (i.1 + 1))
  change
    ⟪(c - 1) • g, a • u⟫_ℝ +
        ⟪s • g, s⁻¹ • (((1 - M.q) * A) • x - (c * a) • u)⟫_ℝ =
      ⟪g, ((1 - M.q) * A) • x - a • u⟫_ℝ
  simp only [real_inner_smul_left, real_inner_smul_right,
    inner_sub_right]
  have hs' : s ≠ 0 := by simpa [s] using hs
  field_simp [hs']
  ring

theorem terminal_block_identity
    (q U a s : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hsq : s ^ 2 = q * (1 - q)) (x u : E) :
    ‖a • u‖ ^ 2 +
        ‖s⁻¹ • (((1 - q) * U) • x - ((1 - q) * a) • u)‖ ^ 2 =
      (1 - q) * U ^ 2 * ‖x‖ ^ 2 +
        (1 / q) * ‖((1 - q) * U) • x - a • u‖ ^ 2 := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hsq
    norm_num at hsq
    rcases hsq with hsq | hsq
    · linarith
    · linarith
  simp only [norm_smul, Real.norm_eq_abs, norm_sub_sq_real,
    real_inner_smul_left, real_inner_smul_right, mul_pow, sq_abs]
  have hsInvSq : s⁻¹ ^ 2 = 1 / (q * (1 - q)) := by
    rw [inv_pow, hsq]
    field_simp
  rw [hsInvSq]
  field_simp [ne_of_gt hq0, ne_of_gt (sub_pos.mpr hq1)]
  ring

end ITEMf
