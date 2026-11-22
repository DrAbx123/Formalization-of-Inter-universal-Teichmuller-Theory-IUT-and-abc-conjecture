/-
S1791 probe: abstract coproduct-component complement (focused)
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

noncomputable section
open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace S1791Probe

variable {C : Type u} [Category.{v} C]
variable [HasFiniteCoproducts C]
variable {ι : Type w} [Fintype ι]
variable (comp : ι → C)

def subFam (S : Set ι) : {k // S k} → C := fun k => comp k.1
def compFam (S : Set ι) : {k // ¬ S k} → C := fun k => comp k.1

noncomputable def subIncl (c : Cofan comp) (S : Set ι) [DecidablePred S] :
    (∐ subFam comp S) ⟶ c.pt :=
  Cofan.IsColimit.desc (coproductIsCoproduct (subFam comp S))
    (fun k => c.inj k.1)

noncomputable def compIncl (c : Cofan comp) (S : Set ι) [DecidablePred S] :
    (∐ compFam comp S) ⟶ c.pt :=
  Cofan.IsColimit.desc (coproductIsCoproduct (compFam comp S))
    (fun k => c.inj k.1)

theorem subIncl_fac (c : Cofan comp) (S : Set ι) [DecidablePred S]
    (k : {k // S k}) :
    Sigma.ι (subFam comp S) k ≫ subIncl comp c S = c.inj k.1 := by
  change Sigma.ι (subFam comp S) k ≫
    Cofan.IsColimit.desc (coproductIsCoproduct (subFam comp S))
      (fun k => c.inj k.1) = c.inj k.1
  exact Cofan.IsColimit.fac (coproductIsCoproduct (subFam comp S))
    (fun k => c.inj k.1) k

theorem compIncl_fac (c : Cofan comp) (S : Set ι) [DecidablePred S]
    (k : {k // ¬ S k}) :
    Sigma.ι (compFam comp S) k ≫ compIncl comp c S = c.inj k.1 := by
  change Sigma.ι (compFam comp S) k ≫
    Cofan.IsColimit.desc (coproductIsCoproduct (compFam comp S))
      (fun k => c.inj k.1) = c.inj k.1
  exact Cofan.IsColimit.fac (coproductIsCoproduct (compFam comp S))
    (fun k => c.inj k.1) k

noncomputable def combinedCofan (S : Set ι) [DecidablePred S]
    (T : C) (f : (∐ subFam comp S) ⟶ T) (g : (∐ compFam comp S) ⟶ T) :
    Cofan comp :=
  Cofan.mk T (fun k =>
    if h : S k then Sigma.ι (subFam comp S) ⟨k, h⟩ ≫ f
    else Sigma.ι (compFam comp S) ⟨k, h⟩ ≫ g)

noncomputable def descMap (c : Cofan comp) (hc : IsColimit c) (S : Set ι) [DecidablePred S]
    {T : C} (f : (∐ subFam comp S) ⟶ T) (g : (∐ compFam comp S) ⟶ T) :
    c.pt ⟶ T :=
  IsColimit.desc hc (combinedCofan comp S T f g)

theorem subIncl_descMap (c : Cofan comp) (hc : IsColimit c) (S : Set ι) [DecidablePred S]
    {T : C} (f : (∐ subFam comp S) ⟶ T) (g : (∐ compFam comp S) ⟶ T) :
    subIncl comp c S ≫ descMap comp c hc S f g = f := by
  apply Sigma.hom_ext
  intro k
  rw [← Category.assoc, subIncl_fac]
  change c.inj k.1 ≫ IsColimit.desc hc (combinedCofan comp S T f g) =
    Sigma.ι (subFam comp S) k ≫ f
  rw [Cofan.IsColimit.inj_desc (combinedCofan comp S T f g) hc k.1]
  change (if h : S k.1 then Sigma.ι (subFam comp S) ⟨k.1, h⟩ ≫ f
    else Sigma.ι (compFam comp S) ⟨k.1, h⟩ ≫ g) = Sigma.ι (subFam comp S) k ≫ f
  rw [dif_pos k.2]

theorem compIncl_descMap (c : Cofan comp) (hc : IsColimit c) (S : Set ι) [DecidablePred S]
    {T : C} (f : (∐ subFam comp S) ⟶ T) (g : (∐ compFam comp S) ⟶ T) :
    compIncl comp c S ≫ descMap comp c hc S f g = g := by
  apply Sigma.hom_ext
  intro k
  rw [← Category.assoc, compIncl_fac]
  change c.inj k.1 ≫ IsColimit.desc hc (combinedCofan comp S T f g) =
    Sigma.ι (compFam comp S) k ≫ g
  rw [Cofan.IsColimit.inj_desc (combinedCofan comp S T f g) hc k.1]
  change (if h : S k.1 then Sigma.ι (subFam comp S) ⟨k.1, h⟩ ≫ f
    else Sigma.ι (compFam comp S) ⟨k.1, h⟩ ≫ g) = Sigma.ι (compFam comp S) k ≫ g
  rw [dif_neg k.2]

end S1791Probe