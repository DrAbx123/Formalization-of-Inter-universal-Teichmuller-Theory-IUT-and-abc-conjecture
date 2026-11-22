import tmp.sheaf.xif.paper.S1392SeparableOfRootCountActual
import tmp.sheaf.xif.paper.S1393XRepFiberBoundActual
import tmp.sheaf.xif.paper.S1366PrePsiSeparabilityFix
import tmp.sheaf.xif.paper.S1379TorsionCardinalityActual
/-! # S1396: separability integration
Detection + l-torsion cardinality give S1329ConcreteSeparable via the actual
S1366 counting theorem.  S1392/S1393 are the root-count/fiber-bound Tau Ceti
ports consumed by that counting argument; cardinality and Kappa are not reproved. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1396SeparabilityIntegrationActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual
open LeanFormal.IUT.XiFPaper.S1366PrePsiSeparabilityFix
open LeanFormal.IUT.XiFPaper.S1379TorsionCardinalityActual
universe u
variable {l : PrimeGeFive}
theorem s1396ConcreteSeparable_of_detection_and_cardinality
    (hdet : S1366TorsionDetection l)
    (hcard : S1366TorsionCardinality l) :
    S1329ConcreteSeparable l :=
  s1366ConcreteSeparable_of_inputs l hdet hcard
theorem s1396ConcreteSeparable_of_criterion_and_cardinality
    (hcrit : S1329ConcreteCriterion l)
    (hcard : S1366TorsionCardinality l) :
    S1329ConcreteSeparable l :=
  s1366ConcreteSeparable_of_criterion_and_cardinality l hcrit hcard
end LeanFormal.IUT.XiFPaper.S1396SeparabilityIntegrationActual
