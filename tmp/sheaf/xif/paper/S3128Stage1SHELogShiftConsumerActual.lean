import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

structure S3128Stage1SHELogShiftSpec : Prop where
  shift : ∀ (m m' : Int) (j : SignedLabel l.value),
    oneColumnLogReadout J m j = oneColumnLogReadout J m' j
  theta : ∀ (m : Int) (j : SignedLabel l.value),
    oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j)
  q_shift : ∀ m : Int, J.oneColumnQ m = J.oneColumnQ (m + 1)

theorem S3128Stage1SHELogShiftSpec_ofSource :
    S3128Stage1SHELogShiftSpec (J := J) :=
  { shift := fun m m' j => oneColumnLogReadout_shift J m m' j
    theta := fun m j => oneColumnLogReadout_theta J m j
    q_shift := fun m => oneColumnQ_shift J m }

#check S3128Stage1SHELogShiftSpec
#check S3128Stage1SHELogShiftSpec_ofSource
end LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftConsumerActual