import tmp.sheaf.xif.paper.S2554CanonicalEssSurjActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import tmp.sheaf.xif.paper.S2521RepresentableStackActual
import tmp.sheaf.xif.paper.S2519InvEquivalenceGoalActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2519InvEquivalenceGoalActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2555ExtractionTransportActual

theorem S2555IsFinite_of_arrowIso
    {X Y B : Scheme} {f : X ⟶ B} {g : Y ⟶ B}
    (e : X ≅ Y) (h : e.hom ≫ g = f) (hg : IsFinite g) : IsFinite f := by
  have hArrow : Arrow.mk f ≅ Arrow.mk g :=
    Arrow.isoMk e (Iso.refl B) (by
      change e.hom ≫ g = f
      exact h)
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) hArrow).mpr hg

theorem S2555Etale_of_arrowIso
    {X Y B : Scheme} {f : X ⟶ B} {g : Y ⟶ B}
    (e : X ≅ Y) (h : e.hom ≫ g = f) (hg : Etale g) : Etale f := by
  have hArrow : Arrow.mk f ≅ Arrow.mk g :=
    Arrow.isoMk e (Iso.refl B) (by
      change e.hom ≫ g = f
      exact h)
  exact (MorphismProperty.arrow_mk_iso_iff (P := @Etale) hArrow).mpr hg

/-- Exact identity-base-change identification still needed for extraction. -/
def S2555ExtractionIso
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S) : Prop := by
  let bc := X.finiteEtale.baseChange S2482AffineOver S2519BasePoint
  exact ∃ e : (bc.pullbackScheme).left ≅ S.left,
    e.hom ≫ (S2554CanonicalMap X S hS).left = Over.Hom.left bc.projection

theorem S2555CanonicalData_of_extractionIso
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S)
    (h : S2555ExtractionIso X S hS) :
    S2554CanonicalData X S hS := by
  let bc := X.finiteEtale.baseChange S2482AffineOver S2519BasePoint
  obtain ⟨e, he⟩ := h
  have he' : e.inv ≫ Over.Hom.left (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).projection
      = (S2554CanonicalMap X S hS).left := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine { etale := ?_, finite := ?_ }
  · exact S2555Etale_of_arrowIso e.symm he'
      (X.finiteEtale.hasProperty S2482AffineOver S2519BasePoint).2
  · exact S2555IsFinite_of_arrowIso e.symm he'
      (X.finiteEtale.hasProperty S2482AffineOver S2519BasePoint).1

#check S2555IsFinite_of_arrowIso
#check S2555Etale_of_arrowIso
#check S2555ExtractionIso
#check S2555CanonicalData_of_extractionIso
end LeanFormal.IUT.XiFPaper.S2555ExtractionTransportActual
end