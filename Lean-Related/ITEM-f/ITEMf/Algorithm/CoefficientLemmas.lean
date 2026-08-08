import ITEMf.Algorithm.ModelIdentities
import ITEMf.Spec.Lyapunov

/-!
# Finite-index and coefficient-domain lemmas
-/

set_option autoImplicit false

namespace ITEMf

variable {N : Nat}

@[simp] theorem idxZero_val : (idxZero N).1 = 0 := rfl
@[simp] theorem idxN_val : (idxN N).1 = N := rfl
@[simp] theorem idxLast_val : (idxLast N).1 = N + 1 := rfl
@[simp] theorem idxInterior_val (i : Fin N) :
    (idxInterior i).1 = i.1 + 1 := rfl
@[simp] theorem lyapCoeffIndex_val (i : Fin N) :
    (lyapCoeffIndex i).1 = i.1 + 1 := rfl
@[simp] theorem lyapNextCoeffIndex_val (i : Fin N) :
    (lyapNextCoeffIndex i).1 = i.1 + 2 := rfl
@[simp] theorem lyapPhiIndex_val (i : Fin N) :
    (lyapPhiIndex i).1 = N - i.1 - 1 := rfl
@[simp] theorem interiorLyapIndex_val (i : Fin (N - 1)) :
    (interiorLyapIndex i).1 = i.1 := rfl
@[simp] theorem nextInteriorLyapIndex_val (i : Fin (N - 1)) :
    (nextInteriorLyapIndex i).1 = i.1 + 1 := rfl

@[simp] theorem firstLyapIndex_val (hN : 1 ≤ N) :
    (firstLyapIndex hN).1 = 0 := rfl

@[simp] theorem terminalLyapIndex_val (hN : 1 ≤ N) :
    (terminalLyapIndex hN).1 = N - 1 := rfl

theorem lyapCoeffIndex_first (hN : 1 ≤ N) :
    lyapCoeffIndex (firstLyapIndex hN) =
      (⟨1, by omega⟩ : Fin (N + 2)) := by
  apply Fin.ext
  rfl

theorem lyapCoeffIndex_terminal (hN : 1 ≤ N) :
    lyapCoeffIndex (terminalLyapIndex hN) = idxN N := by
  apply Fin.ext
  simp [lyapCoeffIndex, terminalLyapIndex, idxN]
  omega

theorem lyapNextCoeffIndex_terminal (hN : 1 ≤ N) :
    lyapNextCoeffIndex (terminalLyapIndex hN) = idxLast N := by
  apply Fin.ext
  simp [lyapNextCoeffIndex, terminalLyapIndex, idxLast]
  omega

theorem lyapPhiIndex_terminal (hN : 1 ≤ N) :
    lyapPhiIndex (terminalLyapIndex hN) =
      (⟨0, by omega⟩ : Fin (N + 1)) := by
  apply Fin.ext
  simp [lyapPhiIndex, terminalLyapIndex]
  omega

theorem phi_zero
    (q : ℝ) (C : CoeffData N) :
    phi q C (⟨0, by omega⟩ : Fin (N + 1)) =
      Real.sqrt (1 - q) := by
  simp [phi]

theorem phi_terminal
    (q : ℝ) (C : CoeffData N) :
    phi q C (⟨N, by omega⟩ : Fin (N + 1)) =
      if N = 0 then Real.sqrt (1 - q)
      else ((1 - q) * C.Upsilon + C.a (idxN N)) /
        Real.sqrt (1 - q) := by
  by_cases hN : N = 0
  · subst N
    simp [phi]
  · simp [phi, hN]

namespace ValidCoefficients

theorem upsilon_pos
    {q : ℝ} {C : CoeffData N} (hC : ValidCoefficients q C) :
    0 < C.Upsilon :=
  lt_trans zero_lt_one hC.upsilon_gt_one

theorem upsilon_ne_zero
    {q : ℝ} {C : CoeffData N} (hC : ValidCoefficients q C) :
    C.Upsilon ≠ 0 :=
  ne_of_gt hC.upsilon_pos

theorem a_zero_pos
    {q : ℝ} {C : CoeffData N} (hC : ValidCoefficients q C) :
    0 < C.a (idxZero N) := by
  rw [hC.a_zero]
  exact div_pos zero_lt_one hC.upsilon_pos

theorem a_pos
    {q : ℝ} {C : CoeffData N} (hC : ValidCoefficients q C)
    (i : Fin (N + 2)) :
    0 < C.a i := by
  by_cases hi : i.1 = 0
  · have hz : i = idxZero N := by
      apply Fin.ext
      simpa [idxZero] using hi
    simpa [hz] using hC.a_zero_pos
  · have hlt : (idxZero N).1 < i.1 := by
      change 0 < i.1
      exact Nat.pos_of_ne_zero hi
    exact lt_trans hC.a_zero_pos (hC.a_strict hlt)

theorem a_ne_zero
    {q : ℝ} {C : CoeffData N} (hC : ValidCoefficients q C)
    (i : Fin (N + 2)) :
    C.a i ≠ 0 :=
  ne_of_gt (hC.a_pos i)

end ValidCoefficients

end ITEMf
