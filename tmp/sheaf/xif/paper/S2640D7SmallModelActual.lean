import tmp.sheaf.xif.paper.S2639D7PerPlacePointActual
import Mathlib.CategoryTheory.EssentiallySmall

/-! # S2640: Type 0 small model for D7 per-place local groups -/

noncomputable section
set_option maxHeartbeats 4000000

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual
open LeanFormal.IUT.XiFPaper.S2639D7PerPlacePointActual
open LeanFormal.IUT.Foundations.Geometry

namespace LeanFormal.IUT.XiFPaper.S2640D7SmallModelActual

variable (l : PrimeGeFive)

/-- Conditional Type 0 local group: precompose the geometric fiber functor with
the equivalence to a small model of the finite-etale cover category. -/
noncomputable abbrev S1727PlaceSmallLocalGroup
    (h : EssentiallySmall.{0} (FiniteEtaleCover S1726AffineScheme))
    (v : NumberFieldPlace (S1727A l).K) : Type :=
  letI := h
  Aut ((equivSmallModel (FiniteEtaleCover S1726AffineScheme)).inverse ⋙
    geometricFiberFunctor (S1727PlaceOmega l v)
      (S1727PlaceGeometricPoint l v))

/-- Conditional Type 0 D7 first field. -/
noncomputable def S1727D7FirstFieldSmall
    (h : EssentiallySmall.{0} (FiniteEtaleCover S1726AffineScheme)) :
    S1727D7FirstField l :=
  fun v => S1727PlaceSmallLocalGroup l h v.1

#check S1727PlaceSmallLocalGroup
#check S1727D7FirstFieldSmall
#print axioms S1727D7FirstFieldSmall

end LeanFormal.IUT.XiFPaper.S2640D7SmallModelActual
end
