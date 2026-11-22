import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe13

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

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

noncomputable def obj (A : Algᵒᵖ) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := Base) (structMap A.unop)
    ⟨structMap_isFinite A.unop, structMap_etale A.unop⟩

example (A B C : Algᵒᵖ) (g : A ⟶ B) (h : B ⟶ C) :
    (MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (P := S1733FiniteEtale)
      (F := Scheme.Spec) (X := Base)
      (Opposite.op (CommRingCat.ofHom (g ≫ h).unop.hom.hom.toRingHom)) (by trivial) (by
        show Spec.map (CommRingCat.ofHom (g ≫ h).unop.hom.hom.toRingHom) ≫ structMap C.unop =
          structMap A.unop
        sorry) : obj A ⟶ obj C) =
      (MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (P := S1733FiniteEtale)
        (F := Scheme.Spec) (X := Base)
        (Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom)) (by trivial) (by
          show Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) ≫ structMap B.unop =
            structMap A.unop
          sorry) ≫
      (MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (P := S1733FiniteEtale)
        (F := Scheme.Spec) (X := Base)
        (Opposite.op (CommRingCat.ofHom h.unop.hom.hom.toRingHom)) (by trivial) (by
          show Spec.map (CommRingCat.ofHom h.unop.hom.hom.toRingHom) ≫ structMap C.unop =
            structMap B.unop
          sorry))) := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  trace_state
  sorry

end Probe13
