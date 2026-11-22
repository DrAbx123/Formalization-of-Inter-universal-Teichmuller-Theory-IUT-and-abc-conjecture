import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import tmp.sheaf.xif.paper.S1727SectionsFPrimeActual
import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section
open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual
open LeanFormal.IUT.Foundations.Geometry

namespace LeanFormal.IUT.XiFPaper.S2639D7PerPlacePointActual

variable (l : PrimeGeFive)

noncomputable abbrev S1727PlaceCompletion
    (v : NumberFieldPlace (S1727A l).K) : Type :=
  match v with
  | .finite p => p.maximalIdeal.adicCompletion (S1727A l).K
  | .infinite p => p.Completion

instance S1727PlaceCompletion_field
    (v : NumberFieldPlace (S1727A l).K) :
    Field (S1727PlaceCompletion l v) := by
  cases v with
  | finite p => infer_instance
  | infinite p => infer_instance

instance S1727PlaceCompletion_algebra
    (v : NumberFieldPlace (S1727A l).K) :
    Algebra (S1727A l).K (S1727PlaceCompletion l v) := by
  cases v with
  | finite p => infer_instance
  | infinite p => infer_instance

noncomputable abbrev S1727PlaceOmega
    (v : NumberFieldPlace (S1727A l).K) : Type :=
  AlgebraicClosure (S1727PlaceCompletion l v)

noncomputable def S1727PlacePointRingHom
    (v : NumberFieldPlace (S1727A l).K) :
    S1726CoordinateRing →+* S1727PlaceOmega l v :=
  (algebraMap (S1727A l).K (S1727PlaceOmega l v)).comp
    (S1726PointAlgHom 0 0 S1726Equation_zero_zero).toRingHom

noncomputable def S1727PlaceGeometricPoint
    (v : NumberFieldPlace (S1727A l).K) :
    Spec (CommRingCat.of (S1727PlaceOmega l v)) ⟶ S1726AffineScheme :=
  Spec.map (CommRingCat.ofHom (S1727PlacePointRingHom l v))

noncomputable abbrev S1727PlaceLocalGroup
    (v : NumberFieldPlace (S1727A l).K) : Type 1 :=
  curveEtaleFundamentalGroup (S1727PlaceOmega l v)
    (S1727PlaceGeometricPoint l v)

noncomputable def S1727D7FirstFieldActualLarge :
    (S1727Layer l).valuationCarrier → Type 1 :=
  fun v => S1727PlaceLocalGroup l v.1

theorem S1727D7FirstFieldActualLarge_nonempty :
    Nonempty ((S1727Layer l).valuationCarrier → Type 1) :=
  ⟨S1727D7FirstFieldActualLarge l⟩

#check S1727PlacePointRingHom
#check S1727PlaceGeometricPoint
#check S1727PlaceLocalGroup
#check S1727D7FirstFieldActualLarge
#print axioms S1727D7FirstFieldActualLarge

#check S1727PlaceCompletion
#check S1727PlaceOmega


end LeanFormal.IUT.XiFPaper.S2639D7PerPlacePointActual
end
