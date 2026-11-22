import tmp.sheaf.xif.paper.S2674D7bGeometricSmallActual
import tmp.sheaf.xif.paper.S2617D7bPerPlaceActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual
open LeanFormal.IUT.XiFPaper.S2617D7bPerPlaceActual
open LeanFormal.IUT.XiFPaper.S2674D7bGeometricSmallActual
open LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual
open LeanFormal.IUT.Foundations.Geometry
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2678D7PiCvSupportActual

variable (l : PrimeGeFive)

theorem S2678GeometricSmallModelRequirement :
    GeometricSmallModelRequirement := by
  unfold GeometricSmallModelRequirement
  exact S2674Cover_essentiallySmall

noncomputable def S2678PerPlaceSupply :
    D7bPerPlaceSupply l :=
  D7bPerPlaceSupply.ofGeometricSmallModel l
    (S2678GeometricSmallModelRequirement)

noncomputable def S2678PerPlaceLocalGroupFamily :
    S2617PerPlaceLocalGroupFamily l :=
  S2617PerPlaceLocalGroupFamily.ofPerPlaceSupply
    (S2678PerPlaceSupply l)

noncomputable def S2678SectionFirstMissing :
    S1727SectionFirstMissing l :=
  (S2678PerPlaceLocalGroupFamily l).toD7SectionSupply

theorem S2678PiCvSupport :
    S2617PerPlaceLocalGroupFamilyRequired l := by
  exact ⟨S2678PerPlaceLocalGroupFamily l⟩

theorem S2678SectionSupply :
    Nonempty (S1727SectionFirstMissing l) := by
  exact ⟨S2678SectionFirstMissing l⟩

#check S2678GeometricSmallModelRequirement
#check S2678PerPlaceSupply
#check S2678PerPlaceLocalGroupFamily
#check S2678SectionFirstMissing
#check S2678PiCvSupport
#check S2678SectionSupply
#print axioms S2678PiCvSupport
#print axioms S2678SectionSupply

end LeanFormal.IUT.XiFPaper.S2678D7PiCvSupportActual
end