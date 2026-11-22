import tmp.sheaf.xif.paper.S3128Stage1SHEHDDStage1FourthJointPremiseActual
import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
import tmp.sheaf.xif.paper.SHEOutputActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDStage1FourthJointPremiseActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointSHECompositionActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1FourthJointSHECompositionPremise
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (P : S3128Stage1SHEHDDStage1FourthJointPremise (I := I) (J := J) D C) :
    (∀ (m m' : Int) (j : SignedLabel l.value),
        Real.log (J.oneColumnScale m j) =
          Real.log (J.oneColumnScale m' j))
      ∧ (∀ (m : Int) (j : SignedLabel l.value),
          oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j))
      ∧ HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0} :=
  ⟨P.logShift,
    fun m j => oneColumnLogReadout_theta J m j,
    P.frozen⟩

theorem S3128Stage1FourthJointSHEReadout
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (P : S3128Stage1SHEHDDStage1FourthJointPremise (I := I) (J := J) D C)
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    C.sheLocalization.expression v o =
      (actualSHEOutput I).bundle.localization v unitSection :=
  P.she_readout v o

#check S3128Stage1FourthJointSHECompositionPremise
#check S3128Stage1FourthJointSHEReadout
end LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointSHECompositionActual