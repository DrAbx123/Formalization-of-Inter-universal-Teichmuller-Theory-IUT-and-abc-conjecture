import tmp.sheaf.xif.paper.S3128Stage1OneColumnConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnDownstreamActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1OneColumnDownstream_succ
    (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = oneColumnLogReadout J (m + 1) j :=
  S3128Stage1OneColumn_readout_succ J m j

theorem S3128Stage1OneColumnDownstream_positivePacket
    (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j =
      Real.log ((J.oneColumnPacket m).toPositivePacket.scale j) :=
  S3128Stage1OneColumn_readout_positivePacket J m j

theorem S3128Stage1OneColumnDownstream_q_shift
    (m : Int) : J.oneColumnQ m = J.oneColumnQ (m + 1) :=
  S3128Stage1OneColumn_q_shift J m

theorem S3128Stage1OneColumnDownstream_shift_pair
    (m m' : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = oneColumnLogReadout J m' j := by
  rw [oneColumnLogReadout_shift J m m' j]

#check S3128Stage1OneColumnDownstream_succ
#check S3128Stage1OneColumnDownstream_positivePacket
#check S3128Stage1OneColumnDownstream_q_shift
#check S3128Stage1OneColumnDownstream_shift_pair
end LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnDownstreamActual