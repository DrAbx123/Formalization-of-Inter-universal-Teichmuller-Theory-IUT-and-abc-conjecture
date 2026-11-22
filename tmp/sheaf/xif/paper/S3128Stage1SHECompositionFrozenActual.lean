import tmp.sheaf.xif.paper.S3128Stage1SHECompositionActual
import tmp.sheaf.xif.paper.S3128Stage1HullDetReadoutActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HullDetReadoutActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionFrozenActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Stage 1 SHE composition + frozen hull/det readout, from the actual U13
and U19 components. -/
theorem S3128Stage1SHECompositionAndFrozen :
    S3128Stage1SHECompositionPremise (J := J)
      ∧ HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0} :=
  ⟨S3128Stage1SHECompositionPremise_holds (J := J),
    S3128Stage1HDDDetReadout_spec⟩

#check S3128Stage1SHECompositionAndFrozen
end LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionFrozenActual