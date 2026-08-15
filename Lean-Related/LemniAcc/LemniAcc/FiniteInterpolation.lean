import LemniAcc.Model

/-!
# Inequality for smooth convex functions
-/

open scoped InnerProductSpace

set_option autoImplicit false

namespace LemniAcc

namespace Internal

theorem finite_interpolation
    {d n : Nat}
    (M : SmoothConvexModel (Euclidean d))
    (x : Fin n → Euclidean d) :
    ∀ i j : Fin n,
      M.f (x j) + ⟪M.grad (x j), x i - x j⟫_ℝ +
          (1 / (2 * (M.L : ℝ))) *
            ‖M.grad (x i) - M.grad (x j)‖ ^ 2 ≤
        M.f (x i) := by
  intro i j
  exact M.interpolation (x i) (x j)

end Internal

end LemniAcc
