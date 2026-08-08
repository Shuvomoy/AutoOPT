import Solution

/-!
# Dependency audit for the fourteen O011 public declarations

The local acceptance gate checks that every printed dependency set is contained in
`{propext, Quot.sound, Classical.choice}`.
-/

#print axioms ITEMf.finiteInterpolation
#print axioms ITEMf.oneStepMap
#print axioms ITEMf.orbitComparison
#print axioms ITEMf.targetAngle
#print axioms ITEMf.shootingIffAdmissible
#print axioms ITEMf.coefficientsExistUnique
#print axioms ITEMf.involutionSymmetry
#print axioms ITEMf.explicitRate
#print axioms ITEMf.transformedMemF0
#print axioms ITEMf.threePointIdentity
#print axioms ITEMf.coordinateRelations
#print axioms ITEMf.normIdentities
#print axioms ITEMf.lyapunovMonotone
#print axioms ITEMf.convergence
