import tmp.sheaf.xif.paper.S3128Stage1FourthJointSHECompositionActual
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
open LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointSHECompositionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointSHEDataActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Data-level consumer of the fourth-joint SHE composition: shift, theta,
frozen and readout=unit, packaged for the U13/SHE downstream. -/
structure S3128Stage1FourthJointSHEData
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (P : S3128Stage1SHEHDDStage1FourthJointPremise (I := I) (J := J) D C) : Prop where
  logShift :
    ∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)
  theta :
    ∀ (m : Int) (j : SignedLabel l.value),
      oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j)
  frozen : HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
  readout :
    ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      C.sheLocalization.expression v o =
        (actualSHEOutput I).bundle.localization v unitSection

theorem S3128Stage1FourthJointSHEData_ofFourthJoint
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (P : S3128Stage1SHEHDDStage1FourthJointPremise (I := I) (J := J) D C) :
    S3128Stage1FourthJointSHEData (I := I) (J := J) D C P :=
  { logShift := P.logShift
    theta := fun m j => oneColumnLogReadout_theta J m j
    frozen := P.frozen
    readout := P.she_readout }

#check S3128Stage1FourthJointSHEData
#check S3128Stage1FourthJointSHEData_ofFourthJoint
end LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointSHEDataActual