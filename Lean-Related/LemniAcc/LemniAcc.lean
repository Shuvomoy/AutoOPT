import LemniAcc.Model
import LemniAcc.FiniteInterpolation
import LemniAcc.Lemniscatic.Integral
import LemniAcc.Lemniscatic.Calculus
import LemniAcc.Continuous.Coefficients
import LemniAcc.Continuous.Trajectory
import LemniAcc.Continuous.Lyapunov
import LemniAcc.Continuous.Convergence
import LemniAcc.Discrete.Recurrence.OneStep
import LemniAcc.Discrete.Recurrence.ExistenceUnique
import LemniAcc.Discrete.Recurrence.OmegaBounds
import LemniAcc.Discrete.LyapunovAlgebra
import LemniAcc.Discrete.Iterates
import LemniAcc.Discrete.CanonicalIterates
import LemniAcc.Discrete.Gaps
import LemniAcc.Discrete.LyapunovTerminal
import LemniAcc.Discrete.LyapunovDecrement
import LemniAcc.Discrete.Convergence

/-!
# LemniAcc proof umbrella

This module imports the complete proof closure. The ten theorem-facing public
names are introduced separately by `Solution.lean`; their implementations
live under `LemniAcc.Internal`.
-/
