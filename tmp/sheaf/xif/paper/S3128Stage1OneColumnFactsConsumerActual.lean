import tmp.sheaf.xif.paper.S3128Stage1SHELogShiftActual
import tmp.sheaf.xif.paper.S3128Stage1OneColumnConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftActual
open LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnFactsConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1OneColumnFacts
    (m m' : Int) (j : SignedLabel l.value) :
    oneColumnLogShift J m m' j = 0 ∧
      oneColumnLogReadout J m j = oneColumnLogReadout J (m + 1) j :=
  ⟨oneColumnLogShift_eq_zero J m m' j,
    S3128Stage1OneColumn_readout_succ J m j⟩

theorem S3128Stage1OneColumnFacts_shift_eq
    (m m' : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = oneColumnLogReadout J m' j :=
  oneColumnLogReadout_shift J m m' j

#check S3128Stage1OneColumnFacts
#check S3128Stage1OneColumnFacts_shift_eq
end LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnFactsConsumerActual