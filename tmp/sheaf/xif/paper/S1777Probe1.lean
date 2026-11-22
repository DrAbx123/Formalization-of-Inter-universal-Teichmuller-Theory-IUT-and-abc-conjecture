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

namespace Probe1

/-- The base ring R'. -/
abbrev R : Type := S1726CoordinateRing

/-- The base scheme Spec R'. -/
abbrev Base : Scheme.{0} := S1726AffineScheme

/-- Finite etale R'-algebras. -/
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

/-- The structure morphism Spec A -> Spec R'. -/
noncomputable def structMap (A : Alg) : Scheme.Spec.obj (Opposite.op (CommRingCat.of (↥A))) ⟶ Base :=
  Spec.map (CommRingCat.ofHom (algebraMap R (↥A)))

example (A : Alg) : IsFinite (structMap A) := by
  rw [structMap, IsFinite.SpecMap_iff]
  rw [CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

example (A : Alg) : Etale (structMap A) := by
  rw [structMap, HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale)]
  rw [CommRingCat.hom_ofHom]
  exact RingHom.etale_algebraMap.mpr inferInstance

example (A : Alg) : S1733FiniteEtale (structMap A) :=
  ⟨by rw [structMap, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
     exact RingHom.finite_algebraMap.mpr inferInstance,
   by rw [structMap, HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale),
        CommRingCat.hom_ofHom]
      exact RingHom.etale_algebraMap.mpr inferInstance⟩

/-- The object map. -/
noncomputable def obj (A : Alg) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := Base) (structMap A)
    ⟨by rw [structMap, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
          exact RingHom.finite_algebraMap.mpr inferInstance,
      by rw [structMap, HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale),
            CommRingCat.hom_ofHom]
        exact RingHom.etale_algebraMap.mpr inferInstance⟩

@[simp] lemma obj_left (A : Alg) : (obj A).left = Opposite.op (CommRingCat.of (↥A)) := rfl
@[simp] lemma obj_hom (A : Alg) : (obj A).hom = structMap A := rfl

/-- The morphism map. -/
noncomputable def map {A B : Alg} (g : A ⟶ B) : obj A ⟶ obj B :=
  MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (F := Scheme.Spec) (X := Base)
    (Opposite.op (CommRingCat.ofHom g.unop.hom.toRingHom)) (by trivial) (by
      show Spec.map (CommRingCat.ofHom g.unop.hom.toRingHom) ≫ structMap B = structMap A
      rw [structMap, structMap, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      ext x
      exact (g.unop.hom.commutes x).symm)

#check @obj
#check @map

end Probe1
