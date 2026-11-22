import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.ZMod.Basic

open CategoryTheory
open scoped Bicategory

set_option autoImplicit false

namespace Probe2436

abbrev X : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ
abbrev S : AddCommGrpCat.{0} := AddCommGrpCat.of ℚ
abbrev T : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod 2)

noncomputable def f : X ⟶ S := AddCommGrpCat.ofHom (Int.castAddHom ℚ)
noncomputable def m : X ⟶ T := AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))

instance : Mono f := by
  constructor
  intro Z g₁ g₂ h
  rw [← AddCommGrpCat.ofHom_hom g₁, ← AddCommGrpCat.ofHom_hom g₂]
  congr 1
  apply AddMonoidHom.ext
  intro x
  have hx := congrFun (congrArg (fun (k : Z ⟶ S) => (k : Z → ℚ)) h) x
  simp only [ConcreteCategory.comp_apply] at hx
  exact Int.cast_injective hx

lemma zmod_two_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> decide

lemma hom_rat_zmod_two (M : S ⟶ T) : M = AddCommGrpCat.ofHom 0 := by
  rw [← AddCommGrpCat.ofHom_hom M, ← AddCommGrpCat.ofHom_hom (AddCommGrpCat.ofHom 0 : S ⟶ T)]
  congr 1
  apply AddMonoidHom.ext
  intro q
  have hq : q = (2 : ℕ) • (q / 2) := by
    rw [nsmul_eq_mul]
    ring
  calc
    (AddCommGrpCat.Hom.hom M) q
        = (AddCommGrpCat.Hom.hom M) ((2 : ℕ) • (q / 2)) := congrArg _ hq
    _ = (2 : ℕ) • (AddCommGrpCat.Hom.hom M) (q / 2) := map_nsmul _ 2 _
    _ = 0 := by
          rw [two_nsmul]
          exact zmod_two_add_self _
    _ = (AddCommGrpCat.Hom.hom (AddCommGrpCat.ofHom 0 : S ⟶ T)) q := by simp

lemma m_ne_zero : m ≠ AddCommGrpCat.ofHom 0 := by
  intro hm
  have hval := congrArg (fun (k : X ⟶ T) => (k : ℤ → ZMod 2) 1) hm
  simp [m] at hval

noncomputable def yonedaCat : (AddCommGrpCat.{0})ᵒᵖ ⥤ Cat.{0,0} where
  obj U := Cat.of (Discrete (U.unop ⟶ T))
  map {U V} g := (Discrete.functor (fun h : U.unop ⟶ T => Discrete.mk (g.unop ≫ h))).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro i
    rfl
  map_comp {U V W} f g := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro i
    simp [Category.assoc]

noncomputable def F : Pseudofunctor (LocallyDiscrete (AddCommGrpCat.{0})ᵒᵖ) Cat.{0,0} :=
  yonedaCat.toPseudofunctor'

def HasEffectiveDescent {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{0,0})
    {S : C} {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ S) : Prop :=
  (F.toDescentData f).EssSurj

noncomputable def D : F.DescentData (fun _ : Unit => f) where
  obj _ := Discrete.mk m
  hom := by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    obtain rfl : i₁ = () := Subsingleton.elim i₁ ()
    obtain rfl : i₂ = () := Subsingleton.elim i₂ ()
    have h : f₁ = f₂ := (cancel_mono f).mp (by rw [hf₁, hf₂])
    subst h
    exact 𝟙 _
  pullHom_hom := by
    intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    obtain rfl : i₁ = () := Subsingleton.elim i₁ ()
    obtain rfl : i₂ = () := Subsingleton.elim i₂ ()
    haveI : Subsingleton ((F.map gf₁.op.toLoc).toFunctor.obj (Discrete.mk m) ⟶
        (F.map gf₂.op.toLoc).toFunctor.obj (Discrete.mk m)) :=
      Discrete.instSubsingletonDiscreteHom _ _
    exact Subsingleton.elim _ _
  hom_self := by
    intro Y q i g hg
    obtain rfl : i = () := Subsingleton.elim i ()
    haveI : Subsingleton ((F.map g.op.toLoc).toFunctor.obj (Discrete.mk m) ⟶
        (F.map g.op.toLoc).toFunctor.obj (Discrete.mk m)) :=
      Discrete.instSubsingletonDiscreteHom _ _
    exact Subsingleton.elim _ _
  hom_comp := by
    intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    obtain rfl : i₁ = () := Subsingleton.elim i₁ ()
    obtain rfl : i₂ = () := Subsingleton.elim i₂ ()
    obtain rfl : i₃ = () := Subsingleton.elim i₃ ()
    haveI : Subsingleton ((F.map f₁.op.toLoc).toFunctor.obj (Discrete.mk m) ⟶
        (F.map f₃.op.toLoc).toFunctor.obj (Discrete.mk m)) :=
      Discrete.instSubsingletonDiscreteHom _ _
    exact Subsingleton.elim _ _

lemma D_obj : D.obj () = (Discrete.mk m : Discrete (X ⟶ T)) := rfl

theorem not_effectiveDescent_singleton :
    ¬ HasEffectiveDescent F (fun _ : Unit => f) := by
  intro h
  obtain ⟨M, ⟨e⟩⟩ := h.mem_essImage D
  rcases M with ⟨M'⟩
  have h2 : f ≫ M' = m := by
    have hmor : (Discrete.mk (f ≫ M') : Discrete (X ⟶ T)) ⟶ (Discrete.mk m : Discrete (X ⟶ T)) :=
      e.hom.hom ()
    obtain ⟨⟨heq⟩⟩ := hmor
    simpa using heq
  have hzero : f ≫ (AddCommGrpCat.ofHom (0 : ℚ →+ ZMod 2)) =
      AddCommGrpCat.ofHom (0 : ℤ →+ ZMod 2) := by
    change AddCommGrpCat.ofHom (Int.castAddHom ℚ) ≫ AddCommGrpCat.ofHom (0 : ℚ →+ ZMod 2) = _
    rw [← AddCommGrpCat.ofHom_comp]
  have hM : M' = AddCommGrpCat.ofHom (0 : ℚ →+ ZMod 2) := hom_rat_zmod_two M'
  have h3 : f ≫ M' = AddCommGrpCat.ofHom (0 : ℤ →+ ZMod 2) := by
    rw [hM]
    exact hzero
  have : m = AddCommGrpCat.ofHom (0 : ℤ →+ ZMod 2) := by rw [← h2, h3]
  exact m_ne_zero this

end Probe2436
