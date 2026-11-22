/-
# S1914: the coherent mono/direct-summand field --- the transport from the
  recorded component-factorization first missing, and the equivalence route

## The question

S1867 reduced the mono/direct-summand field on the coherent covers to the exact
first-missing package

  `S1867MonoFirstMissing` =
    (exists finite coproducts on the S1728 weak cover category) /\
    (`S1867MonoComponentFactorization`: the underlying ambient map of every
      coherent mono satisfies S1791's `MonoComponentFactorizationAPI`) /\
    (`S1867MonoApexCoherent`: every ambient complement apex of a coherent mono
      is isomorphic to a strict object).

S1867 left the transport implication `S1867MonoTransport` unproved, with the
remark that a monomorphism of the full subcategory `S1856StrictSub` need not be
a monomorphism of the ambient S1728 category.  This file settles the categorical
transport and pins the remaining geometric input exactly.

## What is proved here

1. `S1914MonoTransport_holds`: `S1867MonoTransport` is a theorem.  From the
   recorded package we obtain the ambient complement `Z0` by S1791's
   `exists_complement_of_componentFactorization` (the complement is *built* as
   the complementary sub-coproduct of the component decomposition), use
   `S1867MonoApexCoherent` to replace `Z0` by a strict object, and then create
   the binary coproduct in `S1856StrictSub` from the ambient colimit.  The
   creation step is the usual full-subcategory creation of a colimit whose apex
   lies in the subcategory; no complement is postulated.

2. `S1914MonoApexCoherent_of_essImage`: the equivalence gap
   `S1867CoherentEssImage` implies the apex-coherence half.  Every ambient
   cover is then isomorphic to the underlying cover of a coherent cover, so the
   complement apex is strict up to isomorphism.

3. `S1914Mono_hom_of_essImage`: under `S1867CoherentEssImage`, a
   monomorphism of the strict image is a monomorphism of the ambient category.
   The proof tests cancellation against an arbitrary ambient object, replaces it
   by an isomorphic strict object, and cancels the isomorphism.  This is the
   precise place where the essential-image hypothesis is used: without it a
   monomorphism of the full subcategory need not be an ambient monomorphism.

4. `S1914MonoComponentFactorization_of_complement`: conversely, an ambient
   complement of an ambient map produces a S1791 component factorization.  The
   two-term decomposition is built from the two legs of the binary cofan; the
   selected component is compared with the coproduct over the one-element index
   by `coproductUniqueIso`.  This is a genuine construction, not a choice of a
   complement.

5. The equivalence route.  From `S1867CoherentEssImage`, S1791's ambient
   component factorization, and finite coproducts, the recorded package
   `S1867MonoFirstMissing` follows.  With S1763's ambient mono/direct-summand
   data instead of S1791's API, item 3 supplies ambient monicity and item 4
   converts the ambient complement into a component factorization, so

     `S1867CoherentEssImage` + `S1763MonoDirectSummandData` + finite coproducts
       -> `S1867MonoFirstMissing`.

   Since S1833 supplies finite coproducts from `S1833FirstMissing`, the same
   conclusion holds from `S1833FirstMissing` in place of the finite-coproduct
   hypothesis.

## Exact first missing

The direct route is *not* reducible to S1791's mono-only API: as S1867 already
records, `S1867MonoComponentFactorization` asks for the component
factorization of the underlying ambient map of a coherent mono, and that map
need not be a monomorphism of the ambient category.  The exact first missing is
therefore the pair

  `S1867MonoComponentFactorization` + `S1867MonoApexCoherent`

together with finite coproducts, i.e. exactly `S1867MonoFirstMissing`.  What
this file adds is that this package *does* imply the mono/direct-summand field
on the strict image, and that the equivalence route supplies both halves from
`S1867CoherentEssImage` and the ambient mono data.  No fake complement, no
extra axiom, no `sorry`.

## Honest boundary

The geometric statements `S1833FirstMissing`, S1791's ambient component
factorization, `S1763MonoDirectSummandData` and `S1867CoherentEssImage` are
used as hypotheses; none is asserted here.  The categorical implications
between them and the recorded package are proved outright.  The audit at the
end prints the axiom footprint of the proved statements.
-/

import tmp.sheaf.xif.paper.S1867CoherentQuotientsActual
import tmp.sheaf.xif.paper.S1833ActualCoverCoproductsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1914CoherentMonoActual

open CategoryTheory
open CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1763CoverQuotientsActual
open LeanFormal.IUT.XiFPaper.S1791MonoComplementActual
open LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1856CoherentLimitsActual
open LeanFormal.IUT.XiFPaper.S1867CoherentQuotientsActual

attribute [local instance] S1728ActualCategory11 S1854CoherentCategory11

universe u v

/-! ## 1. Apex coherence from the essential image -/

/-- The equivalence gap implies the apex-coherence half of the first missing:
every ambient cover is isomorphic to the underlying cover of a coherent cover,
so an ambient complement apex is strict up to isomorphism. -/
theorem S1914MonoApexCoherent_of_essImage
    (hEss : S1867CoherentEssImage) : S1867MonoApexCoherent := by
  intro X Y i hi Z u hcol
  obtain ⟨C, ⟨e⟩⟩ := hEss Z
  exact ⟨⟨C.cover, ⟨C, rfl⟩⟩, ⟨e.symm⟩⟩

/-- The recorded first-missing package from its two geometric halves and the
finite-coproduct input. -/
theorem S1914MonoFirstMissing_of_components
    [hFC : HasFiniteCoproducts S1728Cover]
    (hComp : @S1867MonoComponentFactorization hFC)
    (hApex : S1867MonoApexCoherent) :
    S1867MonoFirstMissing :=
  ⟨hFC, hComp, hApex⟩

/-- The same package with the apex half supplied by the essential-image gap. -/
theorem S1914MonoFirstMissing_of_essImage_components
    [hFC : HasFiniteCoproducts S1728Cover]
    (hComp : @S1867MonoComponentFactorization hFC)
    (hEss : S1867CoherentEssImage) :
    S1867MonoFirstMissing :=
  S1914MonoFirstMissing_of_components hComp
    (S1914MonoApexCoherent_of_essImage hEss)

/-- The recorded package from S1833's affine comparison, which supplies finite
coproducts on the weak cover category. -/
theorem S1914MonoFirstMissing_of_S1833
    (h1833 : S1833FirstMissing)
    (hComp : @S1867MonoComponentFactorization
      (S1833HasFiniteCoproducts_of_firstMissing h1833))
    (hApex : S1867MonoApexCoherent) :
    S1867MonoFirstMissing := by
  letI hFC : HasFiniteCoproducts S1728Cover :=
    S1833HasFiniteCoproducts_of_firstMissing h1833
  exact ⟨hFC, hComp, hApex⟩

/-! ## 2. The transport on the strict image -/

/-- **The recorded transport is a theorem.**  The ambient complement is built
from S1791's component factorization, its apex is replaced by a strict object
using `S1867MonoApexCoherent`, and the binary coproduct is created in the full
subcategory `S1856StrictSub`.  This is the implication S1867 left open. -/
theorem S1914MonoTransport_holds : S1867MonoTransport := by
  intro hmiss X Y i hi
  obtain ⟨hFC, hComp, hApex⟩ := hmiss
  letI : HasFiniteCoproducts S1728Cover := hFC
  obtain ⟨Z0, u0, ⟨hc0⟩⟩ :=
    S1791Abstract.exists_complement_of_componentFactorization (C := S1728Cover)
      i.hom (hComp i)
  obtain ⟨P, ⟨e⟩⟩ := hApex i Z0 u0 ⟨hc0⟩
  have hc1 : IsColimit (BinaryCofan.mk i.hom (e.inv ≫ u0)) :=
    BinaryCofan.isColimitCompRightIso (BinaryCofan.mk i.hom u0) e.inv hc0
  let u : P ⟶ Y := ObjectProperty.homMk (e.inv ≫ u0)
  refine ⟨P, u, ⟨?_⟩⟩
  refine BinaryCofan.IsColimit.mk (BinaryCofan.mk i u)
    (fun {T} f g =>
      ObjectProperty.homMk (BinaryCofan.IsColimit.desc hc1 f.hom g.hom)) ?_ ?_ ?_
  · intro T f g
    apply ObjectProperty.hom_ext
    change i.hom ≫ BinaryCofan.IsColimit.desc hc1 f.hom g.hom = f.hom
    exact BinaryCofan.IsColimit.inl_desc hc1 f.hom g.hom
  · intro T f g
    apply ObjectProperty.hom_ext
    change (e.inv ≫ u0) ≫ BinaryCofan.IsColimit.desc hc1 f.hom g.hom = g.hom
    exact BinaryCofan.IsColimit.inr_desc hc1 f.hom g.hom
  · intro T f g m hm1 hm2
    apply ObjectProperty.hom_ext
    change m.hom = BinaryCofan.IsColimit.desc hc1 f.hom g.hom
    apply BinaryCofan.IsColimit.hom_ext hc1
    · change i.hom ≫ m.hom =
        i.hom ≫ BinaryCofan.IsColimit.desc hc1 f.hom g.hom
      have hm1' : i.hom ≫ m.hom = f.hom :=
        congrArg (fun k : X ⟶ T => k.hom) hm1
      rw [hm1']
      exact (BinaryCofan.IsColimit.inl_desc hc1 f.hom g.hom).symm
    · change (e.inv ≫ u0) ≫ m.hom =
        (e.inv ≫ u0) ≫ BinaryCofan.IsColimit.desc hc1 f.hom g.hom
      have hm2' : (e.inv ≫ u0) ≫ m.hom = g.hom :=
        congrArg (fun k : P ⟶ T => k.hom) hm2
      rw [hm2']
      exact (BinaryCofan.IsColimit.inr_desc hc1 f.hom g.hom).symm

/-! ## 3. Monicity of the underlying map under the essential image -/

/-- **A coherent mono is an ambient mono once the coherent covers are essentially
surjective.**  The proof is the direct cancellation argument: an arbitrary
ambient test object is replaced by an isomorphic strict object, the
subcategory monomorphism cancels the two test maps, and the cover isomorphism is
then cancelled. -/
theorem S1914Mono_hom_of_essImage (hEss : S1867CoherentEssImage)
    {X Y : S1856StrictSub} (i : X ⟶ Y) [Mono i] : Mono i.hom := by
  refine ⟨fun {W} (g h : W ⟶ X.obj) hgh => ?_⟩
  obtain ⟨C, ⟨e⟩⟩ := hEss W
  let X' : S1856StrictSub := ⟨C.cover, ⟨C, rfl⟩⟩
  let g' : X' ⟶ X := ObjectProperty.homMk (e.hom ≫ g)
  let h' : X' ⟶ X := ObjectProperty.homMk (e.hom ≫ h)
  have hgh' : g' ≫ i = h' ≫ i := by
    apply ObjectProperty.hom_ext
    simp [g', h', Category.assoc, hgh]
  have hEq : g' = h' := (cancel_mono i).mp hgh'
  have hg' : e.hom ≫ g = e.hom ≫ h := by
    simpa [g', h'] using congrArg (fun k : X' ⟶ X => k.hom) hEq
  exact (cancel_epi e.hom).mp hg'

/-! ## 4. From an ambient complement to a component factorization -/

/-- The lifted binary index type, in the universe of `S1728Cover`. -/
abbrev S1914Index : Type 1 := ULift.{1} WalkingPair

instance S1914Index.fintype : Fintype S1914Index where
  elems := {ULift.up WalkingPair.left, ULift.up WalkingPair.right}
  complete := by
    intro x
    cases x with
    | up j => cases j <;> simp

/-- The two components of the decomposition attached to a binary complement.
The index is a lifted `WalkingPair`, so the two-term cofan is the binary cofan
reindexed along `Equiv.ulift`. -/
def S1914Comp (A Z : S1728Cover) : S1914Index → S1728Cover :=
  fun k => pairFunction A Z (Equiv.ulift k)

/-- The selected component of the two-term decomposition. -/
abbrev S1914Subset : Set S1914Index := {k | k.down = WalkingPair.left}

instance S1914SubsetDecidable : DecidablePred S1914Subset :=
  fun k => by
    by_cases h : k.down = WalkingPair.left
    · exact isTrue h
    · exact isFalse h

/-- The canonical selected index. -/
def S1914Sel : {k : S1914Index // S1914Subset k} :=
  ⟨ULift.up WalkingPair.left, rfl⟩

instance S1914SelUnique : Unique {k : S1914Index // S1914Subset k} where
  default := S1914Sel
  uniq k := by
    obtain ⟨⟨j⟩, hk⟩ := k
    cases j
    · apply Subtype.ext
      rfl
    · change WalkingPair.right = WalkingPair.left at hk
      exact absurd hk (by decide)

/-- The two-term cofan with point the binary-coproduct apex: the binary cofan
reindexed along `Equiv.ulift`. -/
def S1914Cofan {A B Z : S1728Cover} (i : A ⟶ B) (u : Z ⟶ B) :
    Cofan (S1914Comp A Z) :=
  let c : Cofan (pairFunction A Z) := BinaryCofan.mk i u
  Cofan.mk B fun k => c.inj (Equiv.ulift k)

/-- A colimiting binary cofan is a colimiting two-term cofan, by reindexing. -/
noncomputable def S1914Cofan_isColimit {A B Z : S1728Cover} (i : A ⟶ B) (u : Z ⟶ B)
    (hc : IsColimit (BinaryCofan.mk i u)) :
    IsColimit (S1914Cofan i u) :=
  let c : Cofan (pairFunction A Z) := BinaryCofan.mk i u
  (Cofan.isColimitEquivOfEquiv (ε := Equiv.ulift) (c := c)) hc

/-- The coproduct over the one-element selected index is the selected component
itself. -/
noncomputable def S1914SelectedIso (A Z : S1728Cover)
    [HasFiniteCoproducts S1728Cover] :
    A ≅ ∐ (S1791Abstract.subFam (S1914Comp A Z) S1914Subset) :=
  let e := coproductUniqueIso
    (S1791Abstract.subFam (S1914Comp A Z) S1914Subset)
  { hom := e.inv
    inv := e.hom
    hom_inv_id := e.inv_hom_id
    inv_hom_id := e.hom_inv_id }

/-- **A complemented ambient map has a component factorization.**  The
complement is the second component of the two-term decomposition; the selected
component is the first. -/
noncomputable def S1914MonoComponentFactorization_of_complement
    [hFC : HasFiniteCoproducts S1728Cover]
    {A B Z : S1728Cover} (i : A ⟶ B) (u : Z ⟶ B)
    (hc : IsColimit (BinaryCofan.mk i u)) :
    S1791Abstract.MonoComponentFactorization S1728Cover i := by
  let D : S1791Abstract.ComponentDecomposition S1728Cover :=
    { index := S1914Index
      fintype := S1914Index.fintype
      component := S1914Comp A Z
      cofan := S1914Cofan i u
      isColimit := S1914Cofan_isColimit i u hc }
  letI := D.fintype
  refine
    { D := D
      e := Iso.refl B
      subset := S1914Subset
      decidable := inferInstance
      iso := S1914SelectedIso A Z
      i_eq := ?_ }
  dsimp only [S1914SelectedIso]
  change i =
    (coproductUniqueIso
      (S1791Abstract.subFam (S1914Comp A Z) S1914Subset)).inv ≫
      S1791Abstract.subIncl (S1914Comp A Z) (S1914Cofan i u) S1914Subset ≫ 𝟙 B
  erw [Category.comp_id]
  rw [coproductUniqueIso_inv]
  change i =
    Sigma.ι (S1791Abstract.subFam (S1914Comp A Z) S1914Subset) S1914Sel ≫
      S1791Abstract.subIncl (S1914Comp A Z) (S1914Cofan i u) S1914Subset
  rw [S1791Abstract.subIncl_fac (S1914Comp A Z) (S1914Cofan i u)
    S1914Subset S1914Sel]
  change i = Cofan.inj (BinaryCofan.mk i u) WalkingPair.left
  rfl

/-! ## 5. The equivalence route -/

/-- S1791's ambient component-factorization API, stated over the actual S1726
orbicurve. -/
def S1914AmbientMonoFactorization : Prop :=
  ∀ [HasFiniteCoproducts S1728Cover] {A B : S1728Cover} (i : A ⟶ B),
    Mono i → S1791Abstract.MonoComponentFactorizationAPI (C := S1728Cover) i

/-- Under the essential image, S1791's ambient component factorization gives the
recorded component factorization of every coherent mono. -/
theorem S1914MonoComponentFactorization_of_essImage_ambient
    [hFC : HasFiniteCoproducts S1728Cover]
    (hEss : S1867CoherentEssImage)
    (hAmb : S1914AmbientMonoFactorization) :
    @S1867MonoComponentFactorization hFC := by
  intro X Y i hi
  exact hAmb i.hom (S1914Mono_hom_of_essImage hEss i)

/-- Under the essential image, S1763's ambient mono/direct-summand data gives
the recorded component factorization of every coherent mono, via the converse
construction of Section 4. -/
theorem S1914MonoComponentFactorization_of_essImage_monoData
    [hFC : HasFiniteCoproducts S1728Cover]
    (hEss : S1867CoherentEssImage)
    (hMono : S1763MonoDirectSummandData (F := S1726K) (X := S1726Orbicurve)) :
    @S1867MonoComponentFactorization hFC := by
  intro X Y i hi
  obtain ⟨Z, u, ⟨hc⟩⟩ :=
    @hMono X.obj Y.obj i.hom (S1914Mono_hom_of_essImage hEss i)
  exact ⟨S1914MonoComponentFactorization_of_complement i.hom u hc⟩

/-- **The recorded first-missing package from the equivalence route.**  Under
`S1867CoherentEssImage`, S1763's ambient mono/direct-summand data and finite
coproducts, the whole package `S1867MonoFirstMissing` follows. -/
theorem S1914MonoFirstMissing_of_equivalenceRoute
    [hFC : HasFiniteCoproducts S1728Cover]
    (hEss : S1867CoherentEssImage)
    (hMono : S1763MonoDirectSummandData (F := S1726K) (X := S1726Orbicurve)) :
    S1867MonoFirstMissing :=
  ⟨hFC, S1914MonoComponentFactorization_of_essImage_monoData hEss hMono,
    S1914MonoApexCoherent_of_essImage hEss⟩

/-- The same equivalence-route conclusion with finite coproducts supplied by
S1833's affine comparison. -/
theorem S1914MonoFirstMissing_of_equivalenceRoute_S1833
    (h1833 : S1833FirstMissing)
    (hEss : S1867CoherentEssImage)
    (hMono : S1763MonoDirectSummandData (F := S1726K) (X := S1726Orbicurve)) :
    S1867MonoFirstMissing := by
  letI hFC : HasFiniteCoproducts S1728Cover :=
    S1833HasFiniteCoproducts_of_firstMissing h1833
  exact S1914MonoFirstMissing_of_equivalenceRoute hEss hMono

/-- S1867's equivalence-route first missing is exactly the pair
`S1867CoherentEssImage` and the ambient mono/direct-summand data.  This is the
definitional unfolding of `S1867MonoFirstMissingEss`. -/
theorem S1914MonoFirstMissingEss_iff :
    S1867MonoFirstMissingEss ↔
      S1867CoherentEssImage ∧
        S1763MonoDirectSummandData (F := S1726K) (X := S1726Orbicurve) :=
  Iff.rfl

/-- The recorded package from S1867's equivalence-route first missing and finite
coproducts. -/
theorem S1914MonoFirstMissing_of_equivalenceFirstMissing
    [hFC : HasFiniteCoproducts S1728Cover]
    (h : S1867MonoFirstMissingEss) : S1867MonoFirstMissing := by
  rcases h with ⟨hEss, hMono⟩
  exact S1914MonoFirstMissing_of_equivalenceRoute hEss hMono

/-- The recorded package from S1867's equivalence-route first missing and
S1833's affine comparison. -/
theorem S1914MonoFirstMissing_of_equivalenceFirstMissing_S1833
    (h1833 : S1833FirstMissing)
    (h : S1867MonoFirstMissingEss) : S1867MonoFirstMissing := by
  rcases h with ⟨hEss, hMono⟩
  exact S1914MonoFirstMissing_of_equivalenceRoute_S1833 h1833 hEss hMono

/-! ## 6. The exact first-missing statement -/

/-- The direct first-missing package in the exact form consumed by the
transport: finite coproducts, the recorded component factorization, and the
apex coherence.  This is definitionally `S1867MonoFirstMissing`; the point of
the name is to record the precise consumer. -/
def S1914MonoDirectFirstMissing : Prop :=
  ∃ h : HasFiniteCoproducts S1728Cover,
    @S1867MonoComponentFactorization h ∧ S1867MonoApexCoherent

/-- The direct first-missing package is the recorded one. -/
theorem S1914MonoDirectFirstMissing_iff :
    S1914MonoDirectFirstMissing ↔ S1867MonoFirstMissing :=
  Iff.rfl

/-- The transport on the strict image follows from the exact first missing. -/
theorem S1914MonoTransport_of_directFirstMissing
    (h : S1914MonoDirectFirstMissing) : S1867MonoTransport :=
  S1914MonoTransport_holds

/-! ## 7. Checks and audit -/

#check S1914MonoApexCoherent_of_essImage
#check S1914MonoFirstMissing_of_components
#check S1914MonoFirstMissing_of_essImage_components
#check S1914MonoFirstMissing_of_S1833
#check S1914MonoTransport_holds
#check S1914Mono_hom_of_essImage
#check S1914Cofan_isColimit
#check S1914SelectedIso
#check S1914MonoComponentFactorization_of_complement
#check S1914AmbientMonoFactorization
#check S1914MonoComponentFactorization_of_essImage_ambient
#check S1914MonoComponentFactorization_of_essImage_monoData
#check S1914MonoFirstMissing_of_equivalenceRoute
#check S1914MonoFirstMissing_of_equivalenceRoute_S1833
#check S1914MonoFirstMissingEss_iff
#check S1914MonoFirstMissing_of_equivalenceFirstMissing
#check S1914MonoFirstMissing_of_equivalenceFirstMissing_S1833
#check S1914MonoDirectFirstMissing
#check S1914MonoDirectFirstMissing_iff
#check S1914MonoTransport_of_directFirstMissing

#print axioms S1914MonoApexCoherent_of_essImage
#print axioms S1914MonoFirstMissing_of_components
#print axioms S1914MonoFirstMissing_of_essImage_components
#print axioms S1914MonoFirstMissing_of_S1833
#print axioms S1914MonoTransport_holds
#print axioms S1914Mono_hom_of_essImage
#print axioms S1914Cofan_isColimit
#print axioms S1914SelectedIso
#print axioms S1914MonoComponentFactorization_of_complement
#print axioms S1914MonoComponentFactorization_of_essImage_ambient
#print axioms S1914MonoComponentFactorization_of_essImage_monoData
#print axioms S1914MonoFirstMissing_of_equivalenceRoute
#print axioms S1914MonoFirstMissing_of_equivalenceRoute_S1833
#print axioms S1914MonoFirstMissing_of_equivalenceFirstMissing
#print axioms S1914MonoFirstMissing_of_equivalenceFirstMissing_S1833
#print axioms S1914MonoDirectFirstMissing_iff
#print axioms S1914MonoTransport_of_directFirstMissing

end LeanFormal.IUT.XiFPaper.S1914CoherentMonoActual