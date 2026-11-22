import tmp.sheaf.xif.paper.S3128HDDPremiseActual
import tmp.sheaf.xif.paper.S3128Stage1SHECompositionActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128HDDPremiseActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDChainActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Stage 1 SHE/HDD chain: SHE composition premise from U13, HDD frozen
spec from U12. -/
theorem S3128Stage1SHEHDDChain :
    S3128Stage1SHECompositionPremise (J := J)
      ∧ HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0} :=
  ⟨S3128Stage1SHECompositionPremise_holds (J := J),
    S3128Stage1HDD_frozenSpec⟩

#check S3128Stage1SHEHDDChain
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDChainActual