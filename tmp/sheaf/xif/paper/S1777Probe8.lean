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

namespace Probe8

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

example (A B : Algᵒᵖ) (g : A ⟶ B) (x : R) :
    (CommRingCat.ofHom g.unop.hom.hom.toRingHom).hom
        ((CommRingCat.ofHom (algebraMap R (↥B.unop))).hom x) =
      (CommRingCat.ofHom (algebraMap R (↥A.unop))).hom x := by
  exact g.unop.hom.hom.commutes x

example (A B : Algᵒᵖ) (g : A ⟶ B) :
    CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫
        CommRingCat.ofHom g.unop.hom.hom.toRingHom =
      CommRingCat.ofHom (algebraMap R (↥A.unop)) := by
  rw [← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact g.unop.hom.hom.commutes x

-- morphism level: opposite composition
example (A B C : Algᵒᵖ) (g : A ⟶ B) (h : B ⟶ C) :
    (Opposite.op (CommRingCat.ofHom (g ≫ h).unop.hom.hom.toRingHom) : _) =
      Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom) ≫
        Opposite.op (CommRingCat.ofHom h.unop.hom.hom.toRingHom) := by
  change (Opposite.op (CommRingCat.ofHom (g ≫ h).unop.hom.hom.toRingHom) : _) =
    Opposite.op (CommRingCat.ofHom h.unop.hom.hom.toRingHom ≫
      CommRingCat.ofHom g.unop.hom.hom.toRingHom)
  refine congrArg Opposite.op ?_
  rw [CommRingCat.ofHom_comp]
  congr 1
  ext x
  rfl

end Probe8
