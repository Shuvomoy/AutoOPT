import ITEMf.Algorithm.IterateRelations
import ITEMf.Lyapunov.BlockAlgebra

/-!
# Interior two-block rotation identities
-/

open scoped InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : Nat}

private theorem rotate_W_formula
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    let c := cCoeff M.q C j
    let s := sCoeff M.q C j
    let a := C.a (lyapCoeffIndex j)
    let A := C.a (lyapNextCoeffIndex j)
    let x := itemfIterate M C x0 (j.1 + 1) - xStar
    let p := itemfPreviousPlus M C x0 (j.1 + 1) - xStar
    blockRotate c s (W M C x0 xStar j) =
      (((1 - M.q) * A) • x,
        s⁻¹ • (((1 - M.q) * c * A) • x - a • p)) := by
  dsimp only
  let j := interiorLyapIndex i
  let c := cCoeff M.q C j
  let s := sCoeff M.q C j
  let a := C.a (lyapCoeffIndex j)
  let A := C.a (lyapNextCoeffIndex j)
  let x := itemfIterate M C x0 (j.1 + 1) - xStar
  let p := itemfPreviousPlus M C x0 (j.1 + 1) - xStar
  have hs : s ≠ 0 := by
    dsimp [s, j]
    exact interior_s_ne_zero_of_relations M.q_unit hC hN hcoord i
  have hunit : s ^ 2 + c ^ 2 = 1 := by
    simpa [s, c, j] using hcoord.interior_unit i
  apply Prod.ext
  · change
      c • (a • p) +
          s • (s⁻¹ • (((1 - M.q) * A) • x - (c * a) • p)) =
        ((1 - M.q) * A) • x
    simp only [smul_smul, smul_sub]
    field_simp [hs]
    module
  · change
      (-s) • (a • p) +
          c • (s⁻¹ • (((1 - M.q) * A) • x - (c * a) • p)) =
        s⁻¹ • (((1 - M.q) * c * A) • x - a • p)
    have hpcoef :
        (-s) * a - c * s⁻¹ * (c * a) = -(s⁻¹ * a) := by
      calc
        (-s) * a - c * s⁻¹ * (c * a) =
            -(s⁻¹ * ((s ^ 2 + c ^ 2) * a)) := by
              field_simp [hs]
              ring
        _ = -(s⁻¹ * a) := by rw [hunit, one_mul]
    simp only [smul_smul, smul_sub]
    calc
      ((-s) * a) • p +
            ((c * (s⁻¹ * ((1 - M.q) * A))) • x -
              (c * (s⁻¹ * (c * a))) • p) =
          (c * (s⁻¹ * ((1 - M.q) * A))) • x +
            (((-s) * a - c * s⁻¹ * (c * a)) • p) := by module
      _ = (c * (s⁻¹ * ((1 - M.q) * A))) • x +
            (-(s⁻¹ * a)) • p := by rw [hpcoef]
      _ = (s⁻¹ * ((1 - M.q) * c * A)) • x -
            (s⁻¹ * a) • p := by module

private theorem W_next_formula
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    let n := nextInteriorLyapIndex i
    let s := sCoeff M.q C j
    let a := C.a (lyapCoeffIndex j)
    let A := C.a (lyapNextCoeffIndex j)
    let bNext := C.b (lyapNextCoeffIndex j)
    let x := itemfIterate M C x0 (j.1 + 1) - xStar
    let u := M.gradientStep (itemfIterate M C x0 (j.1 + 1)) - xStar
    let p := itemfPreviousPlus M C x0 (j.1 + 1) - xStar
    W M C x0 xStar n =
      (A • u,
        bNext • u +
          (a / s) • (u - p) +
          ((1 - M.q) * A / s) • (u - x)) := by
  dsimp only
  let j := interiorLyapIndex i
  let n := nextInteriorLyapIndex i
  let s := sCoeff M.q C j
  let sn := sCoeff M.q C n
  let cnext := cCoeff M.q C n
  let a := C.a (lyapCoeffIndex j)
  let A := C.a (lyapNextCoeffIndex j)
  let B := C.a (lyapNextCoeffIndex n)
  let bNext := C.b (lyapNextCoeffIndex j)
  let xk := itemfIterate M C x0 (j.1 + 1)
  let x := xk - xStar
  let u := M.gradientStep xk - xStar
  let p := itemfPreviousPlus M C x0 (j.1 + 1) - xStar
  have hs : s ≠ 0 := by
    dsimp [s, j]
    exact interior_s_ne_zero_of_relations M.q_unit hC hN hcoord i
  have hsn : sn ≠ 0 := by
    dsimp [sn, n]
    exact s_ne_zero_of_relations M.q_unit hC hN hcoord _
  have h1q : 1 - M.q ≠ 0 := M.one_sub_q_ne_zero
  have hB : B ≠ 0 := by
    dsimp [B]
    exact hC.a_ne_zero _
  have hidx :
      lyapCoeffIndex n = lyapNextCoeffIndex j := by
    apply Fin.ext
    rfl
  have htime : n.1 = j.1 + 1 := by
    rfl
  have hupdate :=
    itemfIterate_next_interior M C x0 hN hC hcoord i
  dsimp only at hupdate
  have hforward := hcoord.forward n
  have hforward' :
      cnext * A + sn * bNext = (1 - M.q) * B := by
    simpa [cnext, sn, A, B, bNext, n, j, hidx] using hforward
  apply Prod.ext
  · unfold W
    dsimp only
    rw [hidx, htime, itemfPreviousPlus_succ]
  · unfold W
    dsimp only
    rw [hidx, htime, itemfPreviousPlus_succ]
    change
      sn⁻¹ •
          (((1 - M.q) * B) •
              (itemfIterate M C x0 (n.1 + 1) - xStar) -
            (cnext * A) • u) =
        bNext • u + (a / s) • (u - p) +
          ((1 - M.q) * A / s) • (u - x)
    rw [hupdate]
    have hcoef :
        ((1 - M.q) * B) *
            (a * sn / ((1 - M.q) * B * s)) / sn =
          a / s := by
      field_simp [h1q, hB, hs, hsn]
    have hcoef2 :
        ((1 - M.q) * B) *
            (A * sn / (B * s)) / sn =
          (1 - M.q) * A / s := by
      field_simp [hB, hs, hsn]
    have hcoefU :
        (((1 - M.q) * B) - cnext * A) / sn = bNext := by
      field_simp [hsn]
      nlinarith [hforward']
    have hcoef' :
        sn⁻¹ * ((1 - M.q) * B *
            (a * sn / ((1 - M.q) * B * s))) =
          a / s := by
      calc
        sn⁻¹ * ((1 - M.q) * B *
            (a * sn / ((1 - M.q) * B * s))) =
            ((1 - M.q) * B *
              (a * sn / ((1 - M.q) * B * s))) / sn := by ring
        _ = a / s := hcoef
    have hcoef2' :
        sn⁻¹ * ((1 - M.q) * B *
            (A * sn / (B * s))) =
          (1 - M.q) * A / s := by
      calc
        sn⁻¹ * ((1 - M.q) * B *
            (A * sn / (B * s))) =
            ((1 - M.q) * B * (A * sn / (B * s))) / sn := by ring
        _ = (1 - M.q) * A / s := hcoef2
    have hcoefU' :
        sn⁻¹ * ((1 - M.q) * B) -
            sn⁻¹ * (cnext * A) =
          bNext := by
      calc
        sn⁻¹ * ((1 - M.q) * B) -
            sn⁻¹ * (cnext * A) =
            (((1 - M.q) * B) - cnext * A) / sn := by ring
        _ = bNext := hcoefU
    simp only [smul_add, smul_sub, smul_smul]
    rw [hcoef', hcoef2', ← hcoefU']
    dsimp [u, p, x, xk]
    simp only [j, interiorLyapIndex]
    module

private theorem rotate_gap_formula
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    let c := cCoeff M.q C j
    let s := sCoeff M.q C j
    let g := M.shiftedGrad xStar
      (itemfIterate M C x0 (j.1 + 1))
    blockRotate c s (gapBlock M C x0 xStar j) =
      ((1 - c) • g, s • g) := by
  dsimp only
  let j := interiorLyapIndex i
  let c := cCoeff M.q C j
  let s := sCoeff M.q C j
  let g := M.shiftedGrad xStar
    (itemfIterate M C x0 (j.1 + 1))
  have hunit : s ^ 2 + c ^ 2 = 1 := by
    simpa [s, c, j] using hcoord.interior_unit i
  have hfirst : c * (c - 1) + s * s = 1 - c := by
    nlinarith
  apply Prod.ext
  · change
      c • ((c - 1) • g) + s • (s • g) =
        (1 - c) • g
    simp only [smul_smul]
    calc
      (c * (c - 1)) • g + (s * s) • g =
          (c * (c - 1) + s * s) • g := by module
      _ = (1 - c) • g := by rw [hfirst]
  · change
      (-s) • ((c - 1) • g) + c • (s • g) =
        s • g
    simp only [smul_smul]
    module

/-- The interior ITEM-f state update is a rotation of the preceding block
after subtracting the scaled shifted-gradient block. -/
theorem interior_W_rotation
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    let n := nextInteriorLyapIndex i
    let c := cCoeff M.q C j
    let s := sCoeff M.q C j
    W M C x0 xStar n =
      blockRotate c s
        (blockSub (W M C x0 xStar j)
          (blockScale (C.Upsilon / M.μ)
            (gapBlock M C x0 xStar j))) := by
  dsimp only
  let j := interiorLyapIndex i
  let n := nextInteriorLyapIndex i
  let c := cCoeff M.q C j
  let s := sCoeff M.q C j
  let a := C.a (lyapCoeffIndex j)
  let A := C.a (lyapNextCoeffIndex j)
  let bNext := C.b (lyapNextCoeffIndex j)
  let xk := itemfIterate M C x0 (j.1 + 1)
  let x := xk - xStar
  let u := M.gradientStep xk - xStar
  let p := itemfPreviousPlus M C x0 (j.1 + 1) - xStar
  let g := M.shiftedGrad xStar xk
  have hs : s ≠ 0 := by
    dsimp [s, j]
    exact interior_s_ne_zero_of_relations M.q_unit hC hN hcoord i
  have hU : C.Upsilon ≠ 0 := hC.upsilon_ne_zero
  have hmu : M.μ = M.q * M.L := M.q_mul_L.symm
  have hgrad :
      u = (1 - M.q) • x - M.L⁻¹ • g := by
    simpa [u, x, g, xk] using M.gradientStep_sub_eq xStar xk
  have hunit : s ^ 2 + c ^ 2 = 1 := by
    simpa [s, c, j] using hcoord.interior_unit i
  have hinverse :
      a = (c + M.q) * A - s * bNext := by
    simpa [a, A, bNext, c, s, j] using hcoord.inverse i
  have hc :
      1 - c = M.q * A / C.Upsilon := by
    dsimp [c, cCoeff, A]
    ring
  have hscale :
      (C.Upsilon / M.μ) * (1 - c) = A / M.L := by
    rw [hc, hmu]
    field_simp [M.q_ne_zero, ne_of_gt M.hL, hU]
  have hsum :
      s * bNext + a + (1 - M.q) * A = (1 + c) * A := by
    nlinarith [hinverse]
  have hsquare :
      C.Upsilon * s ^ 2 = M.q * (1 + c) * A := by
    have hfactor : s ^ 2 = (1 - c) * (1 + c) := by
      nlinarith [hunit]
    rw [hfactor, hc]
    field_simp [hU]
  have hgradientCoefficient :
      bNext / M.L + (a / s) * M.L⁻¹ +
          (((1 - M.q) * A / s) * M.L⁻¹) =
        (C.Upsilon / M.μ) * s := by
    rw [hmu]
    calc
      bNext / M.L + a / s * M.L⁻¹ +
          (1 - M.q) * A / s * M.L⁻¹ =
          (s * bNext + a + (1 - M.q) * A) /
            (s * M.L) := by
              field_simp [ne_of_gt M.hL, hs]
      _ = ((1 + c) * A) / (s * M.L) := by rw [hsum]
      _ = (C.Upsilon / (M.q * M.L)) * s := by
            field_simp [M.q_ne_zero, ne_of_gt M.hL, hs]
            nlinarith [hsquare]
  have hxin :
      s * bNext + a - M.q * A = c * A := by
    nlinarith [hinverse]
  have hxCoefficient :
      (1 - M.q) * bNext +
          (a / s) * (1 - M.q) -
          ((1 - M.q) * A / s) * M.q =
        s⁻¹ * ((1 - M.q) * c * A) := by
    field_simp [hs]
    calc
      (1 - M.q) * (bNext * s + a - M.q * A) =
          (1 - M.q) * (s * bNext + a - M.q * A) := by ring
      _ = (1 - M.q) * (c * A) := by rw [hxin]
      _ = (1 - M.q) * A * c := by ring
  rw [W_next_formula M C x0 xStar hN hC hcoord i]
  rw [blockRotate_sub_scale]
  rw [rotate_W_formula M C x0 xStar hN hC hcoord i]
  rw [rotate_gap_formula M C x0 xStar hN hcoord i]
  apply Prod.ext
  · change
      A • u =
        ((1 - M.q) * A) • x -
          (C.Upsilon / M.μ) • ((1 - c) • g)
    rw [hgrad]
    simp only [smul_sub, smul_smul]
    rw [hscale]
    module
  · change
      bNext • u + (a / s) • (u - p) +
          ((1 - M.q) * A / s) • (u - x) =
        s⁻¹ • (((1 - M.q) * c * A) • x - a • p) -
          (C.Upsilon / M.μ) • (s • g)
    rw [hgrad]
    simp only [smul_sub, smul_add, smul_smul]
    calc
      _ =
          (s⁻¹ * ((1 - M.q) * c * A)) • x -
            (a / s) • p -
            ((C.Upsilon / M.μ) * s) • g := by
              rw [← hxCoefficient, ← hgradientCoefficient]
              module
      _ =
          (s⁻¹ * ((1 - M.q) * c * A)) • x -
            (s⁻¹ * a) • p -
            (C.Upsilon / M.μ * s) • g := by module

end ITEMf
