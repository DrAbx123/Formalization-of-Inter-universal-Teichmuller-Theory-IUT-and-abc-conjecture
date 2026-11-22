/-
S1791 probe: generic structures and API
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace S1791Probe2

open CategoryTheory
open CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The subfamily of components selected by a subset. -/
def subFam (comp : ι → C) (S : Set ι) : {k // S k} → C := fun k => comp k.1

/-- The complementary subfamily. -/
def compFam (comp : ι → C) (S : Set ι) : {k // ¬ S k} → C := fun k => comp k.1

variable [HasFiniteCoproducts C]
variable {ι : Type w} [Fintype ι]
variable (comp : ι → C)

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

noncomputable def binaryCofan_isColimit (c : Cofan comp) (hc : IsColimit c)
    (S : Set ι) [DecidablePred S] :
    IsColimit (BinaryCofan.mk (subIncl comp c S) (compIncl comp c S)) := by
  refine BinaryCofan.IsColimit.mk _
    (fun {T} f g => descMap comp c hc S f g) ?_ ?_ ?_
  · intro T f g
    exact subIncl_descMap comp c hc S f g
  · intro T f g
    exact compIncl_descMap comp c hc S f g
  · intro T f g m hm1 hm2
    change m = descMap comp c hc S f g
    apply Cofan.IsColimit.hom_ext hc
    intro k
    by_cases h : S k
    · have hk : c.inj k = Sigma.ι (subFam comp S) ⟨k, h⟩ ≫ subIncl comp c S := by
        rw [subIncl_fac]
      have hm1' : subIncl comp c S ≫ m = f := hm1
      have hleft : c.inj k ≫ m = Sigma.ι (subFam comp S) ⟨k, h⟩ ≫ f := by
        calc
          c.inj k ≫ m =
              (Sigma.ι (subFam comp S) ⟨k, h⟩ ≫ subIncl comp c S) ≫ m := by rw [hk]; rfl
          _ = Sigma.ι (subFam comp S) ⟨k, h⟩ ≫ (subIncl comp c S ≫ m) :=
            Category.assoc _ _ _
          _ = Sigma.ι (subFam comp S) ⟨k, h⟩ ≫ f := by rw [hm1']
      have hright : c.inj k ≫ descMap comp c hc S f g =
          Sigma.ι (subFam comp S) ⟨k, h⟩ ≫ f := by
        calc
          c.inj k ≫ descMap comp c hc S f g =
              (Sigma.ι (subFam comp S) ⟨k, h⟩ ≫ subIncl comp c S) ≫ descMap comp c hc S f g := by
            rw [hk]; rfl
          _ = Sigma.ι (subFam comp S) ⟨k, h⟩ ≫ (subIncl comp c S ≫ descMap comp c hc S f g) :=
            Category.assoc _ _ _
          _ = Sigma.ι (subFam comp S) ⟨k, h⟩ ≫ f := by rw [subIncl_descMap]
      rw [hleft, hright]
    · have hk : c.inj k = Sigma.ι (compFam comp S) ⟨k, h⟩ ≫ compIncl comp c S := by
        rw [compIncl_fac]
      have hm2' : compIncl comp c S ≫ m = g := hm2
      have hleft : c.inj k ≫ m = Sigma.ι (compFam comp S) ⟨k, h⟩ ≫ g := by
        calc
          c.inj k ≫ m =
              (Sigma.ι (compFam comp S) ⟨k, h⟩ ≫ compIncl comp c S) ≫ m := by rw [hk]; rfl
          _ = Sigma.ι (compFam comp S) ⟨k, h⟩ ≫ (compIncl comp c S ≫ m) :=
            Category.assoc _ _ _
          _ = Sigma.ι (compFam comp S) ⟨k, h⟩ ≫ g := by rw [hm2']
      have hright : c.inj k ≫ descMap comp c hc S f g =
          Sigma.ι (compFam comp S) ⟨k, h⟩ ≫ g := by
        calc
          c.inj k ≫ descMap comp c hc S f g =
              (Sigma.ι (compFam comp S) ⟨k, h⟩ ≫ compIncl comp c S) ≫ descMap comp c hc S f g := by
            rw [hk]; rfl
          _ = Sigma.ι (compFam comp S) ⟨k, h⟩ ≫ (compIncl comp c S ≫ descMap comp c hc S f g) :=
            Category.assoc _ _ _
          _ = Sigma.ι (compFam comp S) ⟨k, h⟩ ≫ g := by rw [compIncl_descMap]
      rw [hleft, hright]

/-! ## Component decomposition API -/

structure ComponentDecomposition (C : Type u) [Category.{v} C] where
  index : Type u
  [fintype : Fintype index]
  component : index → C
  cofan : Cofan component
  isColimit : IsColimit cofan

structure MonoComponentFactorization (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    {A B : C} (i : A ⟶ B) where
  D : ComponentDecomposition C
  e : D.cofan.pt ≅ B
  subset : Set D.index
  [decidable : DecidablePred subset]
  iso : letI := D.fintype
        letI := decidable
        A ≅ (∐ (fun k : {k // subset k} => D.component k.1))
  i_eq : letI := D.fintype
         letI := decidable
         i = iso.hom ≫ subIncl D.component D.cofan subset ≫ e.hom

def MonoComponentFactorizationAPI {A B : C} (i : A ⟶ B) : Prop :=
  Nonempty (MonoComponentFactorization C i)

theorem exists_complement_of_componentFactorization
    {A B : C} (i : A ⟶ B)
    (h : MonoComponentFactorizationAPI (C := C) i) :
    ∃ (Z : C) (u : Z ⟶ B), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  rcases h with ⟨F⟩
  letI := F.D.fintype
  letI := F.decidable
  let Z := ∐ (compFam F.D.component F.subset)
  let u : Z ⟶ B := compIncl F.D.component F.D.cofan F.subset ≫ F.e.hom
  let c0 : BinaryCofan (∐ subFam F.D.component F.subset)
      (∐ compFam F.D.component F.subset) :=
    BinaryCofan.mk (subIncl F.D.component F.D.cofan F.subset)
      (compIncl F.D.component F.D.cofan F.subset)
  let c1 : BinaryCofan (∐ subFam F.D.component F.subset)
      (∐ compFam F.D.component F.subset) :=
    BinaryCofan.mk (subIncl F.D.component F.D.cofan F.subset ≫ F.e.hom)
      (compIncl F.D.component F.D.cofan F.subset ≫ F.e.hom)
  have hcore : IsColimit c0 := binaryCofan_isColimit F.D.component F.D.cofan F.D.isColimit F.subset
  have hpost : IsColimit c1 :=
    IsColimit.ofIsoColimit hcore (BinaryCofan.ext F.e rfl rfl)
  have htrans := BinaryCofan.isColimitCompLeftIso c1 F.iso.hom hpost
  refine ⟨Z, u, ⟨?_⟩⟩
  dsimp only [Z, u, c1]
  exact Eq.mp (congrArg (fun x => IsColimit (BinaryCofan.mk x
    (compIncl F.D.component F.D.cofan F.subset ≫ F.e.hom))) F.i_eq.symm) htrans

#check MonoComponentFactorizationAPI
#check exists_complement_of_componentFactorization

end S1791Probe2