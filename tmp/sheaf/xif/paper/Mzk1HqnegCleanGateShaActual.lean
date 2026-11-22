import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1Cor312SignedMagnitudeChecksActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual

/-!
# shehdd A601 hqneg clean gate (log-only)

`hqneg` is a HYPOTHESIS in the resolved chain (`requirementSignedQ D < 0`), never
an axiom.  This gate prints the axiom dependencies of the hqneg-consuming
theorems: any `sorryAx` or custom axiom in the output is a gate failure; expected
only `[propext, Classical.choice, Quot.sound]`.

The hqneg model files `Mzk1HqnegHullModelActual` (hull) and
`Mzk1Cor312HqnegDischargedActual` (mainline) are their owners' files; this gate
does not depend on them and adds no declarations.
-/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual.requirement_cor312
#print axioms LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual.requirement_strict_signed
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual.abc_of_twoEstimates
