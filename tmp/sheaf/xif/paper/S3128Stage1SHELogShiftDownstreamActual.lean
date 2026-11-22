import tmp.sheaf.xif.paper.S3128Stage1SHELogShiftConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftDownstreamActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHELogShiftDownstream_theta
    (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j) :=
  (S3128Stage1SHELogShiftSpec_ofSource (J := J)).theta m j

theorem S3128Stage1SHELogShiftDownstream_shift
    (m m' : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = oneColumnLogReadout J m' j :=
  (S3128Stage1SHELogShiftSpec_ofSource (J := J)).shift m m' j

theorem S3128Stage1SHELogShiftDownstream_q_shift
    (m : Int) : J.oneColumnQ m = J.oneColumnQ (m + 1) :=
  (S3128Stage1SHELogShiftSpec_ofSource (J := J)).q_shift m

#check S3128Stage1SHELogShiftDownstream_theta
#check S3128Stage1SHELogShiftDownstream_shift
#check S3128Stage1SHELogShiftDownstream_q_shift
end LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftDownstreamActual