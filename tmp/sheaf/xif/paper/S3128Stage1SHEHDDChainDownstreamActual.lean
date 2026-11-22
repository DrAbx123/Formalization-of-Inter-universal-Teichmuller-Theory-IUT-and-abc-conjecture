import tmp.sheaf.xif.paper.S3128SHEHDDInterfaceActual
import tmp.sheaf.xif.paper.S3128Stage1SHECompositionActual
import tmp.sheaf.xif.paper.S3128HDDPremiseActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128SHEHDDInterfaceActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual
open LeanFormal.IUT.XiFPaper.S3128HDDPremiseActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDChainDownstreamActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHEHDDChainDownstream
    (D : S1300HDDHullDetSource I) :
    S3128Stage1SHEHDDFourthJointPremise (I := I) (J := J) D
      ∧ S3128Stage1SHECompositionPremise (J := J)
      ∧ HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0} :=
  ⟨S3128Stage1SHEHDDFourthJointPremise_holds (I := I) (J := J) D,
    S3128Stage1SHECompositionPremise_holds (J := J),
    S3128Stage1HDD_frozenSpec⟩

#check S3128Stage1SHEHDDChainDownstream
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDChainDownstreamActual