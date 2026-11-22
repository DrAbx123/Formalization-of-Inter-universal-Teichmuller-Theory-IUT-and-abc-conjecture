import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHELogShiftConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

structure S1300SHELogShiftConsumer : Type where
  readout_shift : ∀ (m m' : Int) (j : SignedLabel l.value),
    oneColumnLogReadout J m j = oneColumnLogReadout J m' j
  q_shift : ∀ m : Int, J.oneColumnQ m = J.oneColumnQ (m + 1)
  theta_eq : ∀ (m : Int) (j : SignedLabel l.value),
    oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j)

noncomputable def S1300SHELogShiftConsumer.of : S1300SHELogShiftConsumer J where
  readout_shift := oneColumnLogReadout_shift J
  q_shift := oneColumnQ_shift J
  theta_eq := oneColumnLogReadout_theta J

#check S1300SHELogShiftConsumer
#check S1300SHELogShiftConsumer.of
end LeanFormal.IUT.XiFPaper.S1300SHELogShiftConsumerActual
end
