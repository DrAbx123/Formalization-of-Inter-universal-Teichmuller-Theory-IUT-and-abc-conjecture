import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3087GenericSourceHodgeFamilyAttempt


/-- The shear prime strip, parameterized by an arbitrary place index type V. -/
noncomputable def S3087Strip (V : Type) (n m : Int) :
    FPrimeStrip.{0, 0, 0} V where
  Pi := fun _ => Multiplicative (Int × Int)
  groupPi := fun _ => inferInstance
  G := fun _ => Multiplicative (Int × Int)
  groupG := fun _ => inferInstance
  proj := fun _ => (sourceHaarActualShearMulEquiv n m :
    Multiplicative (Int × Int) →* Multiplicative (Int × Int))
  proj_surjective := fun _ => (sourceHaarActualShearMulEquiv n m).surjective
  Mon := fun _ => SourceHaarActualValueMonoid
  commMonoidMon := fun _ => inferInstance
  action := fun _ =>
    sourceHaarActualTrivialAction (Multiplicative (Int × Int))
      SourceHaarActualValueMonoid
  degree := fun _ => sourceHaarActualDegree

/-- The shear Hodge theater, parameterized by V. -/
noncomputable def S3087Theater (V : Type)
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (i : SourceTheorem311Index) : HodgeTheater.{0, 0, 0, 0} fiveLabel V where
  arithmetic := A
  primeStrip := S3087Strip V i.1 i.2
  thetaPacket := sourceHaarActualThetaPacket fiveLabel

/-- The generic family target (the family itself is not yet constructed). -/
abbrev S3087FamilyTarget (V : Type) : Type _ :=
  SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} fiveLabel V

/-- The exact remaining family fields needed to build the generic family. -/
structure S3087FamilyObligations (V : Type) where
  strip : Int -> Int -> FPrimeStrip.{0, 0, 0} V
  theater : SourceTheorem311Index -> HodgeTheater.{0, 0, 0, 0} fiveLabel V
  link : forall i j, HodgeTheaterLink (theater i) (theater j)
  link_refl : forall i, link i i = HodgeTheaterLink.refl (theater i)
  link_symm : forall i j, HodgeTheaterLink.symm (link i j) = link j i
  link_trans : forall i j k, HodgeTheaterLink.trans (link i j) (link j k) = link i k

#check S3087Strip
#check S3087Theater
#check S3087FamilyTarget
#check S3087FamilyObligations

end LeanFormal.IUT.XiFPaper.S3087GenericSourceHodgeFamilyAttempt
end