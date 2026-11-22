import tmp.sheaf.xif.paper.GlobalQVFamThetaHullSumActual
import tmp.sheaf.xif.paper.GlobalThetaPilotHullLogVolumeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3085bPerPlaceFormulaActual

variable {l : PrimeGeFive} {V : Type}
variable [Fintype V]
variable (I : OriginalInput.{0,0,0,0,0} l V)
variable (Rimg : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : V ≃ Bad (nativePlaceSelection T))

noncomputable def S3085bHullLog (v : V) : Real :=
  Real.log (I.sourceSetVolume v (I.sourceHolomorphicHull v (Rimg v) n)).toReal

def S3085bPerPlaceFormula : Prop :=
  forall v : V, S3085bHullLog I Rimg n v = localThetaHullLogFormula T (e v)

theorem S3085b_global_eq_of_perPlace
    (h : S3085bPerPlaceFormula I Rimg n T e) :
    (∑ v : V, S3085bHullLog I Rimg n v) =
      ∑ b : Bad (nativePlaceSelection T), localThetaHullLogFormula T b := by
  exact Fintype.sum_equiv e _ _ (fun v => h v)

#check S3085bHullLog
#check S3085bPerPlaceFormula
#check S3085b_global_eq_of_perPlace
#print axioms S3085b_global_eq_of_perPlace

end LeanFormal.IUT.XiFPaper.S3085bPerPlaceFormulaActual
end