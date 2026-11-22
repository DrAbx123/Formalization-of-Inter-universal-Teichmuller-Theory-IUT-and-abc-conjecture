import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1StepXICanonicalInterfaceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi hqneg coercion

Coerces a negative paper q-reading into the negative requirement signed q,
using the green FinalAssembly readout equality. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegCoercionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_hqneg_of_qReading_neg (R : PaperKummerReading T)
    (h : R.qReading < 0) :
    requirementSignedQ (requirementOfReading T R) < 0 := by
  rw [no_defeq_vacuity T R]
  exact h

end LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegCoercionActual

end
