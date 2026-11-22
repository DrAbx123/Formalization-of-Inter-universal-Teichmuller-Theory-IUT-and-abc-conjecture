import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2520SchemeCoverLimitsActual

abbrev S2520Scheme : Scheme := S2482AffineScheme

/-- Terminal finite etale cover of the S2482 affine curve scheme. -/
noncomputable instance S2520HasTerminal :
    HasTerminal (FiniteEtaleCover S2520Scheme) :=
  (LeanFormal.IUT.IUTII.Frobenioid.Example36.finiteEtaleCover_terminalCover_isTerminal S2520Scheme).hasTerminal

/-- Pullbacks of finite etale covers of the S2482 affine curve scheme. -/
theorem S2520HasPullbacks : HasPullbacks (FiniteEtaleCover S2520Scheme) :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.finiteEtaleCoverHasPullbacks S2520Scheme

/-- Finite coproducts of finite etale covers of the S2482 affine scheme. -/
noncomputable instance S2520HasFiniteCoproducts :
    HasFiniteCoproducts (FiniteEtaleCover S2520Scheme) :=
  inferInstance

/-- Finite limits of finite etale covers of the S2482 affine curve scheme. -/
theorem S2520HasFiniteLimits : HasFiniteLimits (FiniteEtaleCover S2520Scheme) := by
  haveI := S2520HasPullbacks
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

#check S2520HasTerminal
#check S2520HasPullbacks
#check S2520HasFiniteCoproducts
#check S2520HasFiniteLimits
#print axioms S2520HasFiniteLimits
#print axioms S2520HasFiniteCoproducts

end LeanFormal.IUT.XiFPaper.S2520SchemeCoverLimitsActual
end
