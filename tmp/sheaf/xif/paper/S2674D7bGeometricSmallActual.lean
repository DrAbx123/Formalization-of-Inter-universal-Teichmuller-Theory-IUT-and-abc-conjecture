import tmp.sheaf.xif.paper.S1814OrbicurveCoversAffineActual
import tmp.sheaf.xif.paper.S2640D7SmallModelActual
import tmp.sheaf.xif.paper.S1727SectionsFPrimeActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual
open LeanFormal.IUT.XiFPaper.S2639D7PerPlacePointActual
open LeanFormal.IUT.XiFPaper.S2640D7SmallModelActual
open LeanFormal.IUT.Foundations.Geometry

namespace LeanFormal.IUT.XiFPaper.S2674D7bGeometricSmallActual

theorem S2674Cover_essentiallySmall :
    EssentiallySmall.{0, 0, 1} (FiniteEtaleCover S1726AffineScheme) :=
  (CategoryTheory.essentiallySmall_congr
    (LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual.S1814SliceEquiv)).1
    S1733Slice_essentiallySmall

variable (l : PrimeGeFive)

noncomputable abbrev S2674PlaceSmallLocalGroup
    (v : NumberFieldPlace (S1727A l).K) : Type :=
  S1727PlaceSmallLocalGroup l S2674Cover_essentiallySmall v

instance S2674PlaceSmallLocalGroup_group
    (v : NumberFieldPlace (S1727A l).K) :
    Group (S2674PlaceSmallLocalGroup l v) := by
  unfold S2674PlaceSmallLocalGroup
  letI := S2674Cover_essentiallySmall
  infer_instance

noncomputable def S2674D7FirstFieldSmall : S1727D7FirstField l :=
  fun v => S2674PlaceSmallLocalGroup l v.1

#check S2674Cover_essentiallySmall
#check S2674PlaceSmallLocalGroup
#check S2674PlaceSmallLocalGroup_group
#check S2674D7FirstFieldSmall
#print axioms S2674Cover_essentiallySmall
#print axioms S2674PlaceSmallLocalGroup_group

end LeanFormal.IUT.XiFPaper.S2674D7bGeometricSmallActual
end
