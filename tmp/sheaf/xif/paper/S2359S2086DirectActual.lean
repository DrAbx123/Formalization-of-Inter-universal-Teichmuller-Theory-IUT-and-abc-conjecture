import tmp.sheaf.xif.paper.S2086ToAAssemblyActual
import tmp.sheaf.xif.paper.S2161BaseChangeAPIActual
import tmp.sheaf.xif.paper.S2357CorrectedD6ApexActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2161BaseChangeAPIActual
open LeanFormal.IUT.XiFPaper.S2357CorrectedD6ApexActual
namespace LeanFormal.IUT.XiFPaper.S2359S2086DirectActual

/-- The exact direct route to S2086CospanGMapFiniteEtale is stack-level
cancellation of representable finite etaleness. -/
abbrev S2359DirectFirstMissing : Type 1 :=
  S2086StackCancellation

/-- If stack cancellation is supplied, the full S2086 input is constructed,
without using the false S2130 two-pullback target. -/
noncomputable def S2359S2086CospanGMapFiniteEtaleOfCancellation
    (hc : S2359DirectFirstMissing) :
    S2086CospanGMapFiniteEtale :=
  S2086CospanGMapFiniteEtaleOfStackCancellation hc

/-- The direct first-missing proposition. -/
def S2359DirectFirstMissingProp : Prop :=
  Nonempty S2359DirectFirstMissing

/-- Definitional restatement of the direct first-missing proposition. -/
theorem S2359DirectFirstMissingProp_iff :
    S2359DirectFirstMissingProp ↔ Nonempty S2359DirectFirstMissing :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2359S2086DirectActual
end