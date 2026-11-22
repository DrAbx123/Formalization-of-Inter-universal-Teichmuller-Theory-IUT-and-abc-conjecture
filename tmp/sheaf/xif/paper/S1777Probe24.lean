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

namespace Probe24

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

#check @CommRingCat.hom_comp
#check @CommRingCat.comp_apply
#check @RingHom.comp_apply

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

lemma sliceHom_algMap_comp {A B : Algᵒᵖ} (φ : obj A ⟶ obj B) :
    CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop =
      CommRingCat.ofHom (algebraMap R (↥A.unop)) := by
  have htri : Scheme.Spec.map φ.left ≫ (obj B).hom = (obj A).hom := φ.w
  have htri' : Spec.map φ.left.unop ≫ structMap B.unop = structMap A.unop := htri
  rw [structMap, structMap, ← Spec.map_comp] at htri'
  exact Spec.map_injective htri'

end Probe24
