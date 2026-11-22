import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.xif.paper.Mzk1PaperLedgerChecksActual
import tmp.sheaf.xif.paper.Mzk1FinalAssemblyShapeActual
import tmp.sheaf.xif.paper.Mzk1Signed312SelfcheckActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalCThetaActual

/-! # Mzk1Stage4MinorWrapupActual (stage4 lane; unique filename)

A574 module: stage4-lane wrap-up of minor green results — paper shape, signed witness,
constant bound, numeric paper ledger.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4MinorWrapupActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1PaperLedgerChecksActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblyShapeActual
open LeanFormal.IUT.XiFPaper.Mzk1Signed312SelfcheckActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalCThetaActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Wrap-up: the paper Cor 3.12 shape at the concrete witness contract. -/
theorem minor_paper_shape :
    Paper312Shape exampleContract.qSigned exampleContract.thetaSigned :=
  paperShape_example

/-- Wrap-up: the signed Cor 3.12 inequality at the concrete witness. -/
theorem minor_signed_inequality :
    -witnessContract.thetaSigned <= -witnessContract.qSigned :=
  witness_signed_inequality

/-- Wrap-up: the constant bound from the final C_Theta consumer. -/
theorem minor_cTheta (R : PaperKummerReading T) (hqneg : R.qReading < 0) :
    -1 <= R.thetaReading / (-R.qReading) :=
  Mzk1Cor312FinalCThetaActual.final_cTheta_ge_neg_one T R hqneg

/-- Wrap-up: the numeric paper ledger contract satisfies Cor 3.12. -/
theorem minor_ledger (L : Real) (hL : 0 < L) :
    Cor312Conclusion (paperLedgerContract L hL (True) trivial (True) trivial
      (True) trivial) :=
  paperLedger_cor312 L hL (True) trivial (True) trivial (True) trivial

#check minor_paper_shape
#check minor_signed_inequality
#check minor_cTheta
#check minor_ledger

end LeanFormal.IUT.XiFPaper.Mzk1Stage4MinorWrapupActual
end
