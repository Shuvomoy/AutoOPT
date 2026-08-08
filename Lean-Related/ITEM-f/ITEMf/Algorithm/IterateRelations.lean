import ITEMf.Algorithm.Coordinates

/-!
# Interior ITEM-f iterate relations

This module rewrites the displayed momentum coefficients into the `sₖ`
coordinates used by the two-block Lyapunov recursion.
-/

open scoped InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : Nat}

private theorem interior_index_relations (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    let n := nextInteriorLyapIndex i
    idxChordLeft (Fin.castSucc n) = lyapCoeffIndex j ∧
      idxChordRight (Fin.castSucc n) = lyapNextCoeffIndex j ∧
      phiCurrentIndex n = lyapPhiIndex j ∧
      phiPreviousIndex n = lyapPhiIndex n := by
  dsimp only
  constructor
  · apply Fin.ext
    rfl
  constructor
  · apply Fin.ext
    rfl
  constructor
  · apply Fin.ext
    simp [phiCurrentIndex, lyapPhiIndex, interiorLyapIndex,
      nextInteriorLyapIndex]
    omega
  · apply Fin.ext
    simp [phiPreviousIndex, lyapPhiIndex, nextInteriorLyapIndex]

private theorem interior_phi_ne_zero
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (hN : 1 ≤ N) (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (i : Fin (N - 1)) :
    phi M.q C (lyapPhiIndex (interiorLyapIndex i)) ≠ 0 := by
  have hs :
      sCoeff M.q C (interiorLyapIndex i) ≠ 0 :=
    interior_s_ne_zero_of_relations M.q_unit hC hN hcoord i
  intro hphi
  apply hs
  simp [sCoeff, hphi]

theorem itemfMomentum_second_interior
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (hN : 1 ≤ N) (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    let n := nextInteriorLyapIndex i
    (itemfMomentumCoefficients M.q C).second n =
      C.a (lyapNextCoeffIndex j) * sCoeff M.q C n /
        (C.a (lyapNextCoeffIndex n) * sCoeff M.q C j) := by
  dsimp only
  let j := interiorLyapIndex i
  let n := nextInteriorLyapIndex i
  obtain ⟨hidx0, hidx1, hphi0, hphi1⟩ :=
    interior_index_relations i
  have hs : sCoeff M.q C j ≠ 0 :=
    interior_s_ne_zero_of_relations M.q_unit hC hN hcoord i
  have hphi : phi M.q C (lyapPhiIndex j) ≠ 0 :=
    interior_phi_ne_zero M C hN hC hcoord i
  have hU : C.Upsilon ≠ 0 := hC.upsilon_ne_zero
  have hA : C.a (lyapNextCoeffIndex j) ≠ 0 := hC.a_ne_zero _
  have hB : C.a (lyapNextCoeffIndex n) ≠ 0 := hC.a_ne_zero _
  have hsqrt : Real.sqrt M.q ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 M.q_pos)
  change
    phi M.q C (phiPreviousIndex n) /
        phi M.q C (phiCurrentIndex n) =
      C.a (lyapNextCoeffIndex j) * sCoeff M.q C n /
        (C.a (lyapNextCoeffIndex n) * sCoeff M.q C j)
  rw [hphi0, hphi1]
  unfold sCoeff
  change
    phi M.q C (lyapPhiIndex n) / phi M.q C (lyapPhiIndex j) =
      C.a (lyapNextCoeffIndex j) *
          (Real.sqrt M.q * C.a (lyapNextCoeffIndex n) *
            phi M.q C (lyapPhiIndex n) / C.Upsilon) /
        (C.a (lyapNextCoeffIndex n) *
          (Real.sqrt M.q * C.a (lyapNextCoeffIndex j) *
            phi M.q C (lyapPhiIndex j) / C.Upsilon))
  field_simp [hs, hphi, hU, hA, hB, hsqrt]

theorem itemfMomentum_first_interior
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (hN : 1 ≤ N) (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    let n := nextInteriorLyapIndex i
    (itemfMomentumCoefficients M.q C).first n =
      C.a (lyapCoeffIndex j) * sCoeff M.q C n /
        ((1 - M.q) * C.a (lyapNextCoeffIndex n) *
          sCoeff M.q C j) := by
  dsimp only
  let j := interiorLyapIndex i
  let n := nextInteriorLyapIndex i
  obtain ⟨hidx0, hidx1, hphi0, hphi1⟩ :=
    interior_index_relations i
  have hs : sCoeff M.q C j ≠ 0 :=
    interior_s_ne_zero_of_relations M.q_unit hC hN hcoord i
  have hphi : phi M.q C (lyapPhiIndex j) ≠ 0 :=
    interior_phi_ne_zero M C hN hC hcoord i
  have hU : C.Upsilon ≠ 0 := hC.upsilon_ne_zero
  have hA : C.a (lyapNextCoeffIndex j) ≠ 0 := hC.a_ne_zero _
  have hB : C.a (lyapNextCoeffIndex n) ≠ 0 := hC.a_ne_zero _
  have hsqrt : Real.sqrt M.q ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 M.q_pos)
  have h1q : 1 - M.q ≠ 0 := M.one_sub_q_ne_zero
  change
    C.a (idxChordLeft (Fin.castSucc n)) *
          phi M.q C (phiPreviousIndex n) /
        ((1 - M.q) * C.a (idxChordRight (Fin.castSucc n)) *
          phi M.q C (phiCurrentIndex n)) =
      C.a (lyapCoeffIndex j) * sCoeff M.q C n /
        ((1 - M.q) * C.a (lyapNextCoeffIndex n) *
          sCoeff M.q C j)
  rw [hidx0, hidx1, hphi0, hphi1]
  unfold sCoeff
  change
    C.a (lyapCoeffIndex j) * phi M.q C (lyapPhiIndex n) /
        ((1 - M.q) * C.a (lyapNextCoeffIndex j) *
          phi M.q C (lyapPhiIndex j)) =
      C.a (lyapCoeffIndex j) *
          (Real.sqrt M.q * C.a (lyapNextCoeffIndex n) *
            phi M.q C (lyapPhiIndex n) / C.Upsilon) /
        ((1 - M.q) * C.a (lyapNextCoeffIndex n) *
          (Real.sqrt M.q * C.a (lyapNextCoeffIndex j) *
            phi M.q C (lyapPhiIndex j) / C.Upsilon))
  field_simp [hs, hphi, hU, hA, hB, hsqrt, h1q]

theorem itemfIterate_next_interior
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 : E) (hN : 1 ≤ N) (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    let n := nextInteriorLyapIndex i
    let xk := itemfIterate M C x0 (j.1 + 1)
    let xkPlus := M.gradientStep xk
    let previousPlus := itemfPreviousPlus M C x0 (j.1 + 1)
    itemfIterate M C x0 (n.1 + 1) =
      xkPlus +
        (C.a (lyapCoeffIndex j) * sCoeff M.q C n /
          ((1 - M.q) * C.a (lyapNextCoeffIndex n) *
            sCoeff M.q C j)) •
          (xkPlus - previousPlus) +
        (C.a (lyapNextCoeffIndex j) * sCoeff M.q C n /
          (C.a (lyapNextCoeffIndex n) * sCoeff M.q C j)) •
          (xkPlus - xk) := by
  dsimp only
  let j := interiorLyapIndex i
  let n := nextInteriorLyapIndex i
  have hfirst :=
    itemfMomentum_first_interior M C hN hC hcoord i
  have hsecond :=
    itemfMomentum_second_interior M C hN hC hcoord i
  dsimp only at hfirst hsecond
  have hstep := itemfIterate_succ M C x0 n
  rw [hfirst, hsecond] at hstep
  simpa [j, n] using hstep

end ITEMf
