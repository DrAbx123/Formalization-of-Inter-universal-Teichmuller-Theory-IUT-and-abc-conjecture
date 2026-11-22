import tmp.sheaf.xif.paper.S2858Z2MapCompActual
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2858Z2SMapFinActualAdapted
open Iut
open LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (ι : X.stack.fiber ⟶ X.stack.fiber)
variable (sq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp ι ι) (Iut.HyperbolicOrbicurve.Hom.id X))

noncomputable def e (g : SignGroup) : Fin 2 :=
  ⟨(Multiplicative.toAdd g).val, by
    have h := ZMod.val_lt (Multiplicative.toAdd g)
    omega⟩

noncomputable def sMapι (g : SignGroup) : X.stack.fiber ⟶ X.stack.fiber :=
  match e g with
  | 0 => 𝟙 X.stack.fiber
  | 1 => ι

theorem sMapι_one : sMapι X ι 1 = 𝟙 X.stack.fiber := rfl
theorem sMapι_gen :
    sMapι X ι (Multiplicative.ofAdd (1 : ZMod 2)) = ι := rfl

theorem eq_one_of_e_zero {g : SignGroup} (h : e g = 0) : g = 1 := by
  rcases signGroup_cases g with h1 | hg
  · exact h1
  · rw [hg] at h
    simp [e] at h

theorem eq_gen_of_e_one {g : SignGroup} (h : e g = 1) :
    g = Multiplicative.ofAdd (1 : ZMod 2) := by
  rcases signGroup_cases g with h1 | hg
  · rw [h1] at h
    simp [e] at h
  · exact hg

noncomputable def sMapCompGroup (f g : SignGroup) :
    sMapι X ι (g * f) ≅ sMapι X ι f ≫ sMapι X ι g :=
  match hf : e f, hg : e g with
  | 0, 0 => by
      rw [eq_one_of_e_zero hf, eq_one_of_e_zero hg]
      simpa [sMapι] using
        (λ_ (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber)).symm
  | 0, 1 => by
      rw [eq_one_of_e_zero hf, eq_gen_of_e_one hg]
      simpa [sMapι] using (λ_ (show X.stack.fiber ⟶ X.stack.fiber from ι)).symm
  | 1, 0 => by
      rw [eq_gen_of_e_one hf, eq_one_of_e_zero hg]
      simpa [sMapι] using (ρ_ (show X.stack.fiber ⟶ X.stack.fiber from ι)).symm
  | 1, 1 => by
      rw [eq_gen_of_e_one hf, eq_gen_of_e_one hg]
      have h : Multiplicative.ofAdd (1 : ZMod 2) *
          Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide
      rw [h]
      simpa [sMapι] using sq.symm

@[simp] theorem sMapCompGroup_one_one :
    sMapCompGroup X ι sq 1 1 =
      (λ_ (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber)).symm := by
  simp [sMapCompGroup, e]

#check sMapCompGroup
#print axioms sMapCompGroup
#print axioms sMapCompGroup_one_one

end LeanFormal.IUT.XiFPaper.S2858Z2SMapFinActualAdapted