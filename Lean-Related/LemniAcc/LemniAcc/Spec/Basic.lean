import Mathlib

/-!
# Proof-free basic declarations for LemniAcc

This module is part of the trusted theorem-statement closure.  It contains
only data and definitions, never theorem implementations.
-/

set_option autoImplicit false

namespace LemniAcc

/-- The finite-dimensional Euclidean space used by the manuscript statements. -/
abbrev Euclidean (d : Nat) := EuclideanSpace ℝ (Fin d)

end LemniAcc
