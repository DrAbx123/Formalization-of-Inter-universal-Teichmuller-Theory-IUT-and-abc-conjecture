import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnCompositionConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1OneColumnComposition_shift
    (m m' : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = oneColumnLogReadout J m' j :=
  oneColumnLogReadout_shift J m m' j

theorem S3128Stage1OneColumnComposition_succ
    (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = oneColumnLogReadout J (m + 1) j :=
  oneColumnLogReadout_succ J m j

theorem S3128Stage1OneColumnComposition_positivePacket
    (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j =
      Real.log ((J.oneColumnPacket m).toPositivePacket.scale j) :=
  oneColumnLogReadout_positivePacket J m j

theorem S3128Stage1OneColumnComposition_q_shift (m : Int) :
    J.oneColumnQ m = J.oneColumnQ (m + 1) :=
  oneColumnQ_shift J m

#check S3128Stage1OneColumnComposition_shift
#check S3128Stage1OneColumnComposition_succ
#check S3128Stage1OneColumnComposition_positivePacket
#check S3128Stage1OneColumnComposition_q_shift
end LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnCompositionConsumerActual