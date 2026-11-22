import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHELogDetConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Input Label Choice)
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Consumer of the two actual components: SHE vertical log-shift and HDD
detTensorPower log-volume scaling, for the same HDD tensor-hull source. -/
theorem S1300SHE_logShift_detTensorPower_consumer
    (D : S1300HDDHullDetSource I) :
    (∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)) ∧
    (∀ S : Set ((i : Fin D.rank) → D.E i),
      D.detData.logVolume (D.detData.detTensorPower S) =
        (D.detData.tensorPowerExponent : ENNReal) * D.detData.logVolume S) :=
  ⟨s1215LogShiftReadoutCompat_actual J, D.detData.logVolume_detTensorPower⟩

#check S1300SHE_logShift_detTensorPower_consumer
end LeanFormal.IUT.XiFPaper.S1300SHELogDetConsumerActual
end
