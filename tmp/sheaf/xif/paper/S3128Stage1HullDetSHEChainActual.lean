import tmp.sheaf.xif.paper.S3128Stage1HullDetReadoutActual
import tmp.sheaf.xif.paper.S3128Stage1SHECompositionActual
import tmp.sheaf.xif.paper.S3128Stage1HDDConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HullDetReadoutActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HullDetSHEChainActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Stage 1 closure consumer: HDD rank + hull/det frozen spec from actual
U16/U19, and the SHE composition premise from actual U13. -/
theorem S3128Stage1HullDetSHEChain
    (D : S1300HDDHullDetSource I) :
    (D.toS1215 (I := I)).rank = D.rank
      ∧ HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
      ∧ S3128Stage1SHECompositionPremise (J := J) :=
  ⟨(S3128Stage1HDDConsumer_rank_lattice D).1,
    S3128Stage1HDDDetReadout_spec,
    S3128Stage1SHECompositionPremise_holds (J := J)⟩

#check S3128Stage1HullDetSHEChain
end LeanFormal.IUT.XiFPaper.S3128Stage1HullDetSHEChainActual