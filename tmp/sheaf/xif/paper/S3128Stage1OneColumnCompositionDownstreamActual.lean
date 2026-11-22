import tmp.sheaf.xif.paper.S3128Stage1OneColumnCompositionConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnCompositionConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnCompositionDownstreamActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1OneColumnCompositionDownstream_facts
    (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = oneColumnLogReadout J (m + 1) j
      ∧ oneColumnLogReadout J m j =
          Real.log ((J.oneColumnPacket m).toPositivePacket.scale j) :=
  ⟨S3128Stage1OneColumnComposition_succ J m j,
    S3128Stage1OneColumnComposition_positivePacket J m j⟩

theorem S3128Stage1OneColumnCompositionDownstream_q
    (m : Int) : J.oneColumnQ m = J.oneColumnQ (m + 1) :=
  S3128Stage1OneColumnComposition_q_shift J m

#check S3128Stage1OneColumnCompositionDownstream_facts
#check S3128Stage1OneColumnCompositionDownstream_q
end LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnCompositionDownstreamActual