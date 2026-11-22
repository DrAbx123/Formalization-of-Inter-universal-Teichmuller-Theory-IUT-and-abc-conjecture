import tmp.sheaf.xif.paper.S2118PastedComparisonTwistActual
import tmp.sheaf.xif.paper.S1827CloseRetractionActual
import tmp.sheaf.xif.paper.S1801LiftEssSurjActual

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Probe

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual

universe u

theorem eq_hom_of_comp_inv_eq_id {C : Type*} [Category C] {A B : C} (a : A ⟶ B)
    (e : A ≅ B) (h : a ≫ e.inv = 𝟙 A) : a = e.hom := by
  calc a = a ≫ 𝟙 B := (Category.comp_id a).symm
    _ = a ≫ (e.inv ≫ e.hom) := by rw [Iso.inv_hom_id]
    _ = (a ≫ e.inv) ≫ e.hom := by rw [Category.assoc]
    _ = 𝟙 A ≫ e.hom := by rw [h]
    _ = e.hom := Category.id_comp e.hom

end Probe
