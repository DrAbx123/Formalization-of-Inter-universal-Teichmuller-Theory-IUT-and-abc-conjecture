import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe3

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

/-- The structure morphism of the spectrum of a finite etale algebra. -/
noncomputable def structMap (A : CommAlgCat.FiniteEtale.{0} R) :
    Spec (CommRingCat.of (↥A)) ⟶ Base :=
  Spec.map (CommRingCat.ofHom (algebraMap R (↥A)))

lemma structMap_isFinite (A : CommAlgCat.FiniteEtale.{0} R) : IsFinite (structMap A) := by
  rw [structMap, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

lemma structMap_etale (A : CommAlgCat.FiniteEtale.{0} R) : Etale (structMap A) := by
  rw [structMap, HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale),
    CommRingCat.hom_ofHom]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- Object map on finite etale algebras. -/
noncomputable def obj (A : Algᵒᵖ) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := Base) (structMap A.unop)
    ⟨structMap_isFinite A.unop, structMap_etale A.unop⟩

@[simp] lemma obj_left (A : Algᵒᵖ) : (obj A).left = Opposite.op (CommRingCat.of (↥A.unop)) := rfl
@[simp] lemma obj_hom (A : Algᵒᵖ) : (obj A).hom = structMap A.unop := rfl

/-- The functor from finite etale algebras to the affine finite-etale slice. -/
noncomputable def sliceFunctor : Algᵒᵖ ⥤ S1733Slice where
  obj := obj
  map {A B} g :=
    MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (P := S1733FiniteEtale)
      (F := Scheme.Spec) (X := Base)
      (Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom)) (by trivial) (by
        show Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) ≫ structMap B.unop =
          structMap A.unop
        rw [structMap, structMap, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        ext x
        exact (g.unop.hom.hom.commutes x).symm)
  map_id A := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show (Opposite.op (CommRingCat.ofHom (𝟙 A).unop.hom.hom.toRingHom) : _) =
      𝟙 (Opposite.op (CommRingCat.of (↥A.unop)))
    simp
  map_comp {A B C} g h := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show (Opposite.op (CommRingCat.ofHom (g ≫ h).unop.hom.hom.toRingHom) : _) =
      Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom) ≫
        Opposite.op (CommRingCat.ofHom h.unop.hom.hom.toRingHom)
    simp

end Probe3
