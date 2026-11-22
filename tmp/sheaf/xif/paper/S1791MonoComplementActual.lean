/-
# S1791: the complement of a mono of finite etale covers, from a component decomposition

## Target

S1763 isolated the per-mono obligation

  `S1763MonoComplementRequired` : for a mono `i : A ⟶ B` of finite etale
  covers of the actual orbicurve, construct a complement cover `Z`, a map
  `u : Z ⟶ B`, and a proof that `BinaryCofan i u` is a colimit.

## What this file proves

The categorical part of the complement is constructed unconditionally from the
connected-component / clopen decomposition data:

* `S1791Abstract.binaryCofan_isColimit`: for any category with finite
  coproducts, a finite coproduct decomposition `B = ∐ C_k` and a subset `S` of
  the components, the two inclusions of the sub-coproduct `∐_{k∈S} C_k` and the
  complementary sub-coproduct `∐_{k∉S} C_k` form a colimiting binary cofan.
  This is a genuine coproduct computation, not an assumed complement.
* `S1791Abstract.exists_complement_of_componentFactorization`: if a mono
  `i : A ⟶ B` is isomorphic to the inclusion of a sub-coproduct of a finite
  component decomposition of `B` (up to an isomorphism of the total space with
  `B`), then the complement `Z` is the coproduct of the remaining components
  and the binary cofan is colimiting.  The complement is *constructed* as
  `∐_{k∉S} C_k`; it is never postulated.
* `S1791MonoComplementRequired_of_clopenComponentFactorization`: the exact
  `S1763MonoComplementRequired` statement for the actual S1728 cover category,
  conditional on the finite coproduct field and the component-factorisation
  datum.
* `S1791MonoDirectSummandData_of_clopenComponentFactorization`: the literal
  S1736 mono/direct-summand field follows from the component-factorisation API
  and finite coproducts.

## Exact first missing

The tree contains no construction of the geometric input used by the theorem:

1. `S1791ComponentDecomposition` (a finite coproduct decomposition of a cover
   into its connected components) has no inhabitant for the actual etale-stack
   cover category.  `EtaleStackOverField` is a bare category-valued pseudofunctor
   satisfying Mathlib's bare `Pseudofunctor.IsStack`; the tree has no
   `Opens`/`IsClopen`/`connectedComponents`/substack API for it.
2. `S1791MonoComponentFactorizationAPI` (the identification of the image of a
   mono as a sub-coproduct of components) has no inhabitant.  The only
   open-immersion notion available is `EtaleStackOpenImmersion`, a
   representable property of a morphism; there is no open or closed substack
   type, no complement of the image of a stack monomorphism, and no proof that
   a mono of finite etale covers is a clopen union of components.
3. The finite-coproduct field `HasFiniteCoproducts` of the actual cover
   category is itself the separate S1736 G2 obligation.  It is an explicit
   hypothesis of the theorem, not a consequence proved here.

Thus the first missing declarations, in dependency order, are
`S1791ComponentDecomposition` and `S1791MonoComponentFactorizationAPI` (with
`HasFiniteCoproducts` as the separate G2 input).  No fake complement, no
`sorry`, no new axiom, and no inhabitant of the target proposition is assumed.

## Axiom footprint

Every declaration below is proved from the three standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`); see the audit at the end.
-/

import tmp.sheaf.xif.paper.S1763CoverQuotientsActual
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1791MonoComplementActual

open CategoryTheory
open CategoryTheory.Limits
open Iut

namespace S1791Abstract

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

end S1791Abstract

/-! ## Specialisation to the actual S1728 cover category -/

section Actual

open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1763CoverQuotientsActual

variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}

/-- The actual S1728 2-isomorphism-quotient category on the finite etale covers. -/
local instance s1791ActualCategory :
    Category.{u + 1, u + 1} (OrbicurveFiniteEtaleCover X) :=
  S1728CoverCategory11 (F := F) (X := X)

/-- The actual cover type. -/
abbrev S1791Cover := OrbicurveFiniteEtaleCover X

/-- The finite component decomposition of a cover, specialised to the actual
cover category.  This is a genuine finite coproduct decomposition: `cofan` has
point the cover and `isColimit` is its universal property. -/
abbrev S1791ComponentDecomposition :=
  S1791Abstract.ComponentDecomposition (C := OrbicurveFiniteEtaleCover X)

/-- The missing geometric package for one mono: a finite component decomposition
of `B`, an isomorphism of its total space with `B`, a subset of the components,
and the identification of `A` with their coproduct so that `i` is the
coproduct inclusion.  This is exactly the clopen component decomposition of the
image of `i` in `B`; it contains no complement and no colimit of the complement. -/
abbrev S1791MonoComponentFactorizationAPI
    [HasFiniteCoproducts (OrbicurveFiniteEtaleCover X)]
    {A B : OrbicurveFiniteEtaleCover X} (i : A ⟶ B) : Prop :=
  S1791Abstract.MonoComponentFactorizationAPI (C := OrbicurveFiniteEtaleCover X) i

/-- **The categorical part of the mono complement.**  If the image of `i` is a
sub-coproduct of a finite component decomposition of `B`, then the complement
exists, is the coproduct of the remaining components, and the binary cofan is
colimiting. -/
theorem S1791MonoComplementRequired_of_clopenComponentFactorization
    [HasFiniteCoproducts (OrbicurveFiniteEtaleCover X)]
    {A B : OrbicurveFiniteEtaleCover X} (i : A ⟶ B) [Mono i]
    (h : S1791MonoComponentFactorizationAPI (F := F) (X := X) i) :
    S1763MonoComplementRequired F X i := by
  have hres :=
    S1791Abstract.exists_complement_of_componentFactorization
      (C := OrbicurveFiniteEtaleCover X) i h
  simpa [S1763MonoComplementRequired] using hres

/-- The global missing API: every mono of actual covers has a finite component
decomposition of its target and is the inclusion of a sub-coproduct. -/
def S1791ClopenComponentFactorizationAPI
    [HasFiniteCoproducts (OrbicurveFiniteEtaleCover X)] : Prop :=
  ∀ {A B : OrbicurveFiniteEtaleCover X} (i : A ⟶ B), Mono i →
    S1791MonoComponentFactorizationAPI (F := F) (X := X) i

/-- **Assembly of the literal S1736 mono/direct-summand field** from the
component-factorisation API and finite coproducts.  The complement is built, not
assumed. -/
theorem S1791MonoDirectSummandData_of_clopenComponentFactorization
    [HasFiniteCoproducts (OrbicurveFiniteEtaleCover X)]
    (h : S1791ClopenComponentFactorizationAPI (F := F) (X := X)) :
    S1763MonoDirectSummandData F X := by
  intro A B i hmono
  exact S1791MonoComplementRequired_of_clopenComponentFactorization
    (F := F) (X := X) i (h i hmono)

/-- The exact first missing geometric input, stated separately from finite
coproducts: every mono has the component-factorisation datum.  No inhabitant is
asserted. -/
def S1791ClopenComponentFactorizationRequired
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) : Prop :=
  ∀ [HasFiniteCoproducts (OrbicurveFiniteEtaleCover X)],
    S1791ClopenComponentFactorizationAPI (F := F) (X := X)

theorem S1791MonoDirectSummandData_of_firstMissing
    [HasFiniteCoproducts (OrbicurveFiniteEtaleCover X)]
    (h : S1791ClopenComponentFactorizationRequired (F := F) (X := X)) :
    S1763MonoDirectSummandData F X :=
  S1791MonoDirectSummandData_of_clopenComponentFactorization (F := F) (X := X) h

end Actual

/-! ## Status markers and axiom audit -/

#check S1791Abstract.MonoComponentFactorizationAPI
#check S1791Abstract.exists_complement_of_componentFactorization
#check S1791MonoComplementRequired_of_clopenComponentFactorization
#check S1791MonoDirectSummandData_of_clopenComponentFactorization
#check S1791ClopenComponentFactorizationRequired

#print axioms S1791Abstract.binaryCofan_isColimit
#print axioms S1791Abstract.exists_complement_of_componentFactorization
#print axioms S1791MonoComplementRequired_of_clopenComponentFactorization
#print axioms S1791MonoDirectSummandData_of_clopenComponentFactorization

end LeanFormal.IUT.XiFPaper.S1791MonoComplementActual
