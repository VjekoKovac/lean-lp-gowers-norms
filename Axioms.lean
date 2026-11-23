module

import Solution
import Lean.Util.CollectAxioms

/-! Print the selected comparison declarations, then audit the transitive axiom
dependencies of every exported theorem and definition in the LpGowers namespace.
The executable audit inspects environment metadata. No proof calls it. -/

#print axioms LpGowers.theorem_1_1
#print axioms LpGowers.theorem_1_2
#print axioms LpGowers.theorem_1_3a
#print axioms LpGowers.theorem_1_4
#print axioms LpGowers.theorem_1_5
#print axioms LpGowers.Checked.subgroupIndicator
#print axioms LpGowers.Checked.marginal
#print axioms LpGowers.Checked.degreeOneExponent
#print axioms LpGowers.Checked.exactMoments
#print axioms LpGowers.Checked.scalarGaussianCorrelation
#print axioms LpGowers.Checked.binaryEnergy
#print axioms LpGowers.Checked.binaryLower
#print axioms LpGowers.Checked.finiteInterpolation
#print axioms LpGowers.Checked.euclideanSharpEstimate
#print axioms LpGowers.Checked.gaussianEquality
#print axioms LpGowers.Checked.euclideanNecessaryConstant
#print axioms LpGowers.Checked.largeSideLimit
#print axioms LpGowers.Checked.lebesgueInequality
#print axioms LpGowers.Checked.degreeInequalities
#print axioms LpGowers.Checked.ordinaryLogConvex
#print axioms LpGowers.Checked.allGaussianEquality
#print axioms LpGowers.Checked.binarySetExponent
#print axioms LpGowers.Checked.binaryEnergyAllDimensions
#print axioms LpGowers.Checked.setAttainment
#print axioms LpGowers.Checked.functionAttainment
#print axioms LpGowers.Checked.productUpper
#print axioms LpGowers.Checked.binaryLargeDegree
#print axioms LpGowers.Checked.nearThreeMoments
#print axioms LpGowers.Checked.binaryBothExponents
#print axioms LpGowers.Checked.diagonalLeakage

#print axioms LpGowers.Checked.binarySharp
#print axioms LpGowers.Checked.criticalExponents

#print axioms LpGowers.Checked.largeSideSharp
#print axioms LpGowers.Checked.largeDegreeLower

#print axioms LpGowers.sharpYoungEquality
#print axioms LpGowers.youngMoment_tendsto_of_lpDist
#print axioms LpGowers.euclideanTheorem_of_affinePrecompact
#print axioms LpGowers.heat_error_le_initial_deficit
#print axioms LpGowers.subsequence_of_interval_approximation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if `LpGowers |>.isPrefixOf name then
      let axioms ← collectAxioms name
      for axName in axioms do
        unless allowed.contains axName do
          throwError "unpermitted axiom {axName} in {name}"
      count := count + 1
  if count == 0 then throwError "no LpGowers declarations found"
  logInfo m!"Audited {count} LpGowers declarations. Permitted axioms: {allowed}."
