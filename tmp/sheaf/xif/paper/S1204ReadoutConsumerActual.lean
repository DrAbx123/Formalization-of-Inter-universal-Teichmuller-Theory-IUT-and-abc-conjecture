import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1204ReadoutConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

structure S1204ReadoutConsumer : Type where
  shift : ∀ (m m' : Int) (j : SignedLabel l.value),
    oneColumnLogReadout I m j = oneColumnLogReadout I m' j
  succ : ∀ (m : Int) (j : SignedLabel l.value),
    oneColumnLogReadout I m j = oneColumnLogReadout I (m + 1) j
  theta : ∀ (m : Int) (j : SignedLabel l.value),
    oneColumnLogReadout I m j = Real.log (I.thetaValueAt m 0 j)
  positivePacket : ∀ (m : Int) (j : SignedLabel l.value),
    oneColumnLogReadout I m j =
      Real.log ((I.oneColumnPacket m).toPositivePacket.scale j)
  q_shift : ∀ m : Int, I.oneColumnQ m = I.oneColumnQ (m + 1)

noncomputable def S1204ReadoutConsumer.of : S1204ReadoutConsumer I where
  shift := oneColumnLogReadout_shift I
  succ := oneColumnLogReadout_succ I
  theta := oneColumnLogReadout_theta I
  positivePacket := oneColumnLogReadout_positivePacket I
  q_shift := oneColumnQ_shift I

#check S1204ReadoutConsumer
#check S1204ReadoutConsumer.of
end LeanFormal.IUT.XiFPaper.S1204ReadoutConsumerActual
end
