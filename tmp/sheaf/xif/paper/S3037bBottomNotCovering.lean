import tmp.sheaf.xif.paper.S3037NonemptyHne
import Mathlib.CategoryTheory.Sites.Sheaf
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3026NonemptyEtaleSite
open LeanFormal.IUT.XiFPaper.S3037NonemptyHne
namespace LeanFormal.IUT.XiFPaper.S3037BottomNotCovering

universe u v

/-- Generic empty-sieve subsingleton lemma. -/
theorem S3037_subsingleton_of_bot_mem
    {C : Type u} [Category C] {J : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type v} (hP : Presheaf.IsSheaf J P)
    {T : C} (hT : (⊥ : Sieve T) ∈ J T) :
    Subsingleton (P.obj (Opposite.op T)) := by
  have h' : Presieve.IsSheaf J P :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hP
  have hfor : Presieve.IsSheafFor P ((⊥ : Sieve T) : Presieve T) :=
    h' (⊥ : Sieve T) hT
  let x : Presieve.FamilyOfElements P ((⊥ : Sieve T) : Presieve T) :=
    fun Y f hf => hf.elim
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomp
    exact h₁.elim
  obtain ⟨t, -, huniq⟩ := hfor x hx
  exact ⟨fun a b => by
    rw [huniq a (fun Y f hf => hf.elim), huniq b (fun Y f hf => hf.elim)]⟩

/-- If a big-site sheaf has a nonsubsingleton section at U, the bottom sieve is
not covering for the induced topology. -/
theorem S3037_bottom_not_mem_of_nonsubsingleton
    (U : S3026NonemptyScheme)
    (P : (Iut.SchemeOverField S2882A6PointwisePseudofunctorActual.K)ᵒᵖ ⥤ Type)
    (hP : Presheaf.IsSheaf
      (Iut.SchemeOverField.etaleTopology S2882A6PointwisePseudofunctorActual.K) P)
    (hns : ¬ Subsingleton (P.obj (Opposite.op U.obj))) :
    ((⊥ : Sieve U) ∉ S3026NonemptySite U) := by
  intro hbot
  let G : Sheaf
      (Iut.SchemeOverField.etaleTopology S2882A6PointwisePseudofunctorActual.K)
      (Type _) := ⟨P, hP⟩
  have hP' : Presheaf.IsSheaf S3026NonemptySite
      (S3026NonemptyProperty.ι.op ⋙ P) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (Functor.op_comp_isSheaf_of_types S3026NonemptyProperty.ι
        S3026NonemptySite
        (Iut.SchemeOverField.etaleTopology S2882A6PointwisePseudofunctorActual.K) G)
  have hsub := S3037_subsingleton_of_bot_mem hP' hbot
  exact hns (by simpa using hsub)

#check S3037_subsingleton_of_bot_mem
#check S3037_bottom_not_mem_of_nonsubsingleton
#print axioms S3037_subsingleton_of_bot_mem
#print axioms S3037_bottom_not_mem_of_nonsubsingleton

end LeanFormal.IUT.XiFPaper.S3037BottomNotCovering