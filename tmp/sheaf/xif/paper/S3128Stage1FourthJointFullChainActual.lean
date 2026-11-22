import tmp.sheaf.xif.paper.S3128Stage1FourthJointCompleteDownstreamActual
import tmp.sheaf.xif.paper.S3128Stage1HDDDetDownstreamActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointCompleteDownstreamActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDDetDownstreamActual
open LeanFormal.IUT.XiFPaper.S3128SHEHDDInterfaceActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointFullChainActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Full FourthJoint chain consumer: HDD rank/hull/det + frozen spec
from the actual HDDDet downstream, and the FourthJoint premise +
SHE composition from the actual complete downstream. -/
theorem S3128Stage1FourthJointFullChain
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    S3128Stage1SHEHDDFourthJointPremise (I := I) (J := J) D
      ∧ S3128Stage1SHECompositionPremise (J := J)
      ∧ (D.toS1215 (I := I)).rank = D.rank
      ∧ (D.toS1215 (I := I)).lattice o v =
          (fun x : (i : Fin D.rank) → D.E i =>
            fun i => D.localEquiv v i (x i)) ''
          @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o)
      ∧ HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
      ∧ Nonempty
          (DetTensorPowerLogVolumeBookkeeping
            (Set ((i : Fin D.rank) → D.E i))) :=
  let C := S3128Stage1FourthJointCompleteDownstream (I := I) (J := J) D
  let H := S3128Stage1HDDDetDownstream (I := I) D o v
  ⟨C.1, C.2.2.2, H.1, H.2.1, C.2.1, C.2.2.1⟩

#check S3128Stage1FourthJointFullChain
end LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointFullChainActual