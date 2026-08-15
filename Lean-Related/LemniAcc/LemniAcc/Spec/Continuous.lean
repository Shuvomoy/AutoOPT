import LemniAcc.Spec.Model
import LemniAcc.Spec.Lemniscatic

/-!
# Proof-free continuous-trajectory interface
-/

open scoped InnerProductSpace Topology
open Set Filter

set_option autoImplicit false

namespace LemniAcc

open Lemniscatic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The exact trajectory interface used by the continuous-time theorem. -/
structure ContinuousTrajectory
    (M : SmoothConvexModel E) (T : ℝ) (x0 : E) where
  X : ℝ → E
  V : ℝ → E
  A : ℝ → E
  X_continuous : ContinuousOn X (Icc (0 : ℝ) T)
  V_continuous : ContinuousOn V (Icc (0 : ℝ) T)
  A_continuous : ContinuousOn A (Icc (0 : ℝ) T)
  X_derivative :
    ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt X (V t) t
  V_derivative :
    ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V (A t) t
  ode :
    ∀ t ∈ Ioo (0 : ℝ) T,
      A t + gamma T t • V t + 2 • M.grad (X t) = 0
  X_zero : X 0 = x0
  V_zero : V 0 = 0

end LemniAcc
