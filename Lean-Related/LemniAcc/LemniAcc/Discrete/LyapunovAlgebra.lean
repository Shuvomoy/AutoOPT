import LemniAcc.Spec.Discrete

/-!
# Scalar algebra for the LemniAcc Lyapunov sequence

This module isolates the rational coefficient identities used when expanding
one decrement of the discrete Lyapunov sequence.  The only mathematical input
is one step of the LemniAcc scalar recurrence.
-/

set_option autoImplicit false

namespace LemniAcc.Discrete

/-- The first scalar identity in the proof of the closed decrement formula. -/
theorem recurrence_scalar_identity_one
    {Ω r s : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hsq : s ^ 2 ≠ 1)
    (hrec : Ω * (r - s) ^ 2 = r * (1 - s ^ 2)) :
    Ω * (plusCoeff s - plusCoeff r) * positionCoeff s + 1 =
      Ω * (minusCoeff s - minusCoeff r) := by
  unfold plusCoeff minusCoeff positionCoeff
  field_simp
  linear_combination -2 * s * hrec

/-- The second scalar identity in the proof of the closed decrement formula. -/
theorem recurrence_scalar_identity_two
    {Ω r s : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hrec : Ω * (r - s) ^ 2 = r * (1 - s ^ 2)) :
    (Ω / 2) *
        ((minusCoeff s - minusCoeff r) ^ 2 -
          (plusCoeff s - plusCoeff r) ^ 2) =
      minusCoeff s := by
  unfold minusCoeff plusCoeff
  field_simp
  nlinarith

/-- `plusCoeff` strictly increases when its argument strictly decreases
inside `(0,1]`. -/
theorem plusCoeff_lt_plusCoeff
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 1) :
    plusCoeff r < plusCoeff s := by
  unfold plusCoeff
  have hrs : 0 < r := lt_trans hs hsr
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (sub_pos.mpr hsr) (sub_pos.mpr (by nlinarith : r * s < 1))]

/-- `minusCoeff` strictly increases when its argument strictly decreases
inside `(0,1]`. -/
theorem minusCoeff_lt_minusCoeff
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 1) :
    minusCoeff r < minusCoeff s := by
  unfold minusCoeff
  have hrs : 0 < r := lt_trans hs hsr
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (sub_pos.mpr hsr) (by nlinarith : 0 < 1 + r * s)]

end LemniAcc.Discrete
