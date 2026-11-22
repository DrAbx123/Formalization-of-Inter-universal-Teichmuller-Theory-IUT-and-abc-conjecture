import tmp.sheaf.xif.paper.S3128Stage1OneColumnConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnAllConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1OneColumnAll
    (m m' : Int) :
    (∀ j : SignedLabel l.value,
        oneColumnLogReadout J m j = oneColumnLogReadout J m' j)
      ∧ J.oneColumnQ m = J.oneColumnQ (m + 1) :=
  ⟨fun j => oneColumnLogReadout_shift J m m' j,
    oneColumnQ_shift J m⟩

theorem S3128Stage1OneColumnAll_succ
    (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = oneColumnLogReadout J (m + 1) j :=
  S3128Stage1OneColumn_readout_succ J m j

#check S3128Stage1OneColumnAll
#check S3128Stage1OneColumnAll_succ
end LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnAllConsumerActual