import tmp.sheaf.xif.paper.S3057ConnectedHomSheaf
import tmp.sheaf.xif.paper.S3037cBottomNotCoveringConcrete
import Mathlib.CategoryTheory.Sites.Over
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3050ConnectedSite
open LeanFormal.IUT.XiFPaper.S3057ConnectedHomSheaf
open LeanFormal.IUT.XiFPaper.S3037BottomNotCovering
open LeanFormal.IUT.XiFPaper.S3037cBottomNotCoveringConcrete
open LeanFormal.IUT.XiFPaper.S3026NonemptyEtaleSite
open LeanFormal.IUT.XiFPaper.S2811IsPrestackActual
namespace LeanFormal.IUT.XiFPaper.S3077bOverBottomNotCovering

abbrev K : Type := S3050ConnectedSite.K

/-- The over-site bottom sieve is not covering. -/
theorem S3077_over_bottom_not_mem
    (S : S3050ConnectedScheme) (T : Over S) :
    ((⊥ : Sieve T) ∉ S3050ConnectedSite.over S T) := by
  intro hbot
  let Tsp : S3026NonemptyScheme := ⟨T.left.obj, T.left.property.1⟩
  let X2 : Iut.SchemeOverField K := S3037cX Tsp
  have hns : ¬ Subsingleton
      ((yoneda.obj X2).obj (Opposite.op T.left.obj)) := by
    intro hsub
    exact S3037cInl_ne_inr Tsp T.left.property.1
      (hsub.elim (S3037cInl Tsp) (S3037cInr Tsp))
  let G : Sheaf (Iut.SchemeOverField.etaleTopology K) (Type _) :=
    ⟨yoneda.obj X2, S2811_yoneda_isSheaf K X2⟩
  let P0 : (S3050ConnectedScheme)ᵒᵖ ⥤ Type _ :=
    S3050ConnectedProperty.ι.op ⋙ yoneda.obj X2
  have hP0 : Presheaf.IsSheaf S3050ConnectedSite P0 :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (Functor.op_comp_isSheaf_of_types S3050ConnectedProperty.ι
        S3050ConnectedSite (Iut.SchemeOverField.etaleTopology K) G)
  let G0 : Sheaf S3050ConnectedSite (Type _) := ⟨P0, hP0⟩
  have hP : Presheaf.IsSheaf (S3050ConnectedSite.over S)
      ((Over.forget S).op ⋙ P0) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (Functor.op_comp_isSheaf_of_types (Over.forget S)
        (S3050ConnectedSite.over S) S3050ConnectedSite G0)
  have hsub := S3037_subsingleton_of_bot_mem hP hbot
  exact hns (by simpa [P0] using hsub)

/-- Over-site hne: every covering sieve has an index. -/
theorem S3077_over_hne
    (S : S3050ConnectedScheme) (T : Over S) (R : Sieve T)
    (hR : R ∈ S3050ConnectedSite.over S T) :
    Nonempty R.arrows.category := by
  by_contra hne
  apply S3077_over_bottom_not_mem S T
  have hRbot : R = ⊥ := by
    ext Y f
    constructor
    · intro hf
      exact False.elim (hne ⟨⟨Over.mk f, hf⟩⟩)
    · intro hf
      exact False.elim hf
  rwa [hRbot] at hR

/-- The S3057 hne premise is actual. -/
theorem S3077_S3057Hne : S3057Hne :=
  fun S T R hR => S3077_over_hne S T R hR

/-- Unconditional separatedness of the connected-site hom presheaf. -/
theorem S3077_homForm_separated
    (S : S3050ConnectedScheme)
    (M N : S3050Q.obj { as := Opposite.op S }) :
    Presheaf.IsSeparated (S3050ConnectedSite.over S)
      (S3050Q.presheafHom M N) :=
  S3057_homForm_separated S3077_S3057Hne S M N

#check S3077_S3057Hne
#check S3077_homForm_separated
#print axioms S3077_homForm_separated
#check S3077_over_bottom_not_mem
#check S3077_over_hne
#print axioms S3077_over_hne

end LeanFormal.IUT.XiFPaper.S3077bOverBottomNotCovering