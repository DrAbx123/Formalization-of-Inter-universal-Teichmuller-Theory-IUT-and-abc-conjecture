import tmp.sheaf.xif.paper.S462Example32PhiIsoGroupLikeActual
import tmp.sheaf.xif.paper.S453DvTriangleMorphismAlgHomActual
import tmp.sheaf.xif.paper.S456RationalInclusionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S477Example32RationalPullbackLawsActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S462Example32PhiIsoGroupLikeActual
open LeanFormal.IUT.XiFPaper.S453DvTriangleMorphismAlgHomActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

lemma example32RationalPullback_eq_arrow
    {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    example32RationalPullback (K := K) f =
      (Units.map (arrowAlgebraMap K f).toMonoidHom).toAdditive := by
  rfl

theorem example32RationalPullback_id (X : Example32SmallBase K) :
    example32RationalPullback (K := K) (𝟙 X) =
      AddMonoidHom.id (Additive (Example32CoverField K X)ˣ) := by
  rw [example32RationalPullback_eq_arrow, arrowAlgebraMap_id]
  simp [Units.map_id]

theorem example32RationalPullback_comp
    {X Y Z : Example32SmallBase K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    example32RationalPullback (K := K) (f ≫ g) =
      (example32RationalPullback (K := K) f).comp
        (example32RationalPullback (K := K) g) := by
  rw [example32RationalPullback_eq_arrow, example32RationalPullback_eq_arrow,
    example32RationalPullback_eq_arrow, arrowAlgebraMap_comp]
  ext x
  simp [MonoidHom.toAdditive]

