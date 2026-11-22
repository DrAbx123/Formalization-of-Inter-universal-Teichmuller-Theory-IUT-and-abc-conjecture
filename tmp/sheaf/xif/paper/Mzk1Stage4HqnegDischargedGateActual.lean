import tmp.sheaf.xif.paper.Mzk1Cor312HqnegDischargedActual

/-! # Mzk1Stage4HqnegDischargedGateActual (stage4 lane; unique filename)

A606 module: stage4 acceptance gate on the mainline hqneg- discharged file — restates
the discharged Cor 3.12 conclusion as a gate and prints its axiom dependencies.
Read-only consumer; the mainline file is not modified.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4HqnegDischargedGateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312HqnegDischargedActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Acceptance gate: the mainline discharged-hqneg file yields the Cor 3.12
conclusion for any strictly negative q-pilot reading. -/
theorem discharged_gate {qRead : Real} (hq : qRead < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T (canonicalReading (T := T) hq)
        (canonicalHqneg (T := T) hq)
        ipl hipl she hshe apt hapt) :=
  Mzk1Cor312HqnegDischargedActual.cor312_hqneg_discharged T hq ipl hipl she hshe apt hapt

#print axioms discharged_gate
#print axioms Mzk1Cor312HqnegDischargedActual.cor312_hqneg_discharged

#check discharged_gate

end LeanFormal.IUT.XiFPaper.Mzk1Stage4HqnegDischargedGateActual
end
