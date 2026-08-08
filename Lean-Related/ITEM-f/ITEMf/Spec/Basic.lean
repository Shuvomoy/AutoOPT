import Mathlib

/-!
# Basic types for analytic ITEM-f

This module contains only notation and proof-free data used by both the
trusted Comparator challenge and the proof-bearing solution.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

/-- The finite-dimensional Euclidean space used in the manuscript. -/
abbrev Euclidean (d : Nat) := EuclideanSpace ℝ (Fin d)

/-- The open unit-interval condition used for the condition ratio `q`. -/
def UnitRatio (q : ℝ) : Prop :=
  0 < q ∧ q < 1

end ITEMf
