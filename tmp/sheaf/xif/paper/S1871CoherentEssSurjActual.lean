/-
# S1871: is every weak cover isomorphic to a coherent cover?

## The question

S1854 constructed the actual category of coherent covers

    S1854CoherentCategory11  :  Category.{1,1} CoherentCover

and the forgetful functor `S1854Forget11 : CoherentCover ⥤ S1728Cover` to the
S1728 category of weak covers (the 2-isomorphism quotient), and proved the
functor full and faithful: the coherent structure restricts the *objects*, not
the homs.  This file reduces the remaining exactness property of the inclusion
(essential surjectivity) to a single geometric statement, and decides the
surrounding questions (the candidate counterexample, the equality version, and
the unit-based refutation route):

    S1871EssSurj :  forall weak A, exists coherent C, C.cover ~= A,

i.e. essential surjectivity of the coherent subcategory in the S1728
2-isomorphism category.  Equivalently, `S1854Forget11.EssSurj`
(`S1871EssSurj_iff_forget_essSurj`).

## What is decided here

1. `S1871IsoOfMapIso`: **covers with the same source and 2-isomorphic structure
   maps are isomorphic in the S1728 2-isomorphism category**, whatever their
   finite-etale data.  The isomorphism is presented by the two identity cover
   maps, whose composites are the classes of the bicategorical unitors.
   `S1871IsoOfMk` is the special case of literally the same source and map.

2. **S1850's doubled cover is NOT a counterexample.**  Its source and structure
   map are those of the terminal cover (`S1850SameSource`, `S1850SameMap`), so by
   item 1 it is isomorphic to the *coherent* terminal cover
   (`S1871DoubledIsoTerminalCoherent`).  Hence

     S1871DoubledCover_not_counterexample :  exists coherent C, C.cover ~= S1850DoubledCover.

   This is the substantive correction to the naive expectation: S1852's
   `S1852DoubledCover_not_coherent` only says that no coherent cover has the
   doubled cover as its *literally equal* underlying cover; it does not, and
   cannot, refute essential surjectivity.

3. The *equality* version is false: `S1871NotForallCoherentEq`,

     not (forall A, exists C, C.cover = A),

   obtained from S1852's refutation of `S1756FirstMissing`.  So the iso version
   `S1871EssSurj` is strictly weaker than the equality version, and the equality
   refutation does not transfer.

4. **The precise reason it does not transfer**: the missing unit 2-cell `S1756Unit`
   is not an invariant of the 2-isomorphism class of a cover.  Concretely
   `S1871Unit_not_iso_invariant`: the doubled cover (no unit, `S1850NoUnit`) is
   isomorphic to the terminal coherent cover (unit).  Consequently the transfer
   principle

     S1871UnitTransfer :  A ~= B -> S1756Unit A -> S1756Unit B

   is false (`S1871NotUnitTransfer`), and the natural derivation
   "essential surjectivity + unit transfer -> S1756FirstMissing" (proved as
   `S1871FirstMissing_of_essSurj_of_unitTransfer`) cannot be used to refute
   essential surjectivity.  The doubled cover refutes the *transfer*, not the
   essential surjectivity.

5. **The positive direction and the exact first missing.**  Essential
   surjectivity is *equivalent* to slice realisation
   (`S1871EssSurj_iff_strongSliceEquiv`):

     def S1871StrongSliceEquivAt (A) : Prop :=
       exists (S' : stack) (f' : S' -> X.stack) (phi : A.source -> S')
         (psi : S' -> A.source), Strong f' /\
         phi >> psi ~= id /\ psi >> phi ~= id /\ phi >> f' ~= A.map.

   So the coherent subcategory is essentially surjective exactly when every
   weak cover's structure map is 2-isomorphic, along an equivalence of its
   source stack, to a strongly finite-etale map.  This is the exact first
   missing: the *construction* of a strong finite-etale structure on a
   slice-isomorphic map.  The direction slice realisation -> essential
   surjectivity is proved outright (`S1871EssSurjAt_of_strongSliceEquivAt`),
   and the converse is free from a cover isomorphism
   (`S1871StrongSliceEquivAt_of_essSurjAt`): no transport of the strong
   structure is needed.

   The refinement with the source fixed (`S1871StrongInSlice`,
   `S1871EssSurj_of_strongInSlice`) also suffices; passing from slice realisation
   to that fixed-source form is the transport `S1871StrongTransfer` (not proved
   here), and with it essential surjectivity is equivalent to strong realisation
   on the nose (`S1871EssSurj_iff_strongRealization`).

   In the tree only the identity class is realised (`S1852IdStrong`;
   conditionally the pullback/coproduct apexes of S1856), so the missing
   statement is satisfiable (the doubled and terminal covers satisfy it,
   `S1871StrongInSliceAt_identityCover`) but not available in general.

## Honest boundary

* No refutation of `S1871EssSurj` is produced, and no proof either.  What is
  decided is: (i) essential surjectivity is *equivalent* to slice realisation of
  strong structures (a proved equivalence, not a reduction with a gap), (ii) the
  only candidate counterexample in the tree is not one, (iii) the equality
  version is false, and (iv) the unit-based refutation route is blocked.
* The exact first missing for the positive direction is the construction in
  `S1871StrongSliceEquiv` (a strong structure on a slice-isomorphic map), or its
  fixed-source refinement `S1871StrongInSlice` / transport `S1871StrongTransfer`;
  none is assumed, and no strong structure is fabricated.  Everything proved
  below uses only the recorded definitions.
* No sorry, no axiom, no placeholder.  Axiom footprint checked at the end.

## References

S1728 (2-isomorphism quotient category), S1733 (models), S1743 (identity-point
base change), S1756 (unit 2-cell), S1850 (doubled presentation), S1852
(coherent cover datum, `S1852ConeEssSurj`), S1854 (coherent category, forgetful
functor), S1809 (quotient/2-isomorphism bookkeeping), S1832 (`S1832Q`, the
explicit class of a cover map).
-/

import tmp.sheaf.xif.paper.S1854CoherentCategoryActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1871CoherentEssSurjActual

open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1809SmallCarrierCategoryActual
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual

/-! The coherent category is a category; fix it as the local instance so that
`CoherentCover ⥤ ...` elaborates. -/
attribute [local instance] S1854CoherentCategory11

universe u

/-! ## 1. The statement, in three equivalent forms -/

/-- Isomorphism of weak covers in the S1728 2-isomorphism category
(`S1728ActualCategory11`, definitionally the instance `S1728CoverCategory11`
on the cover type). -/
abbrev S1871CoverIso (A B : S1728Cover) : Prop := Nonempty (A ≅ B)

/-- **The target statement of S1871**: the coherent subcategory of the S1728
2-isomorphism category is essentially surjective, i.e. every weak cover is
isomorphic to the underlying cover of a coherent cover. -/
def S1871EssSurj : Prop :=
  ∀ A : S1728Cover, ∃ C : CoherentCover, S1871CoverIso C.cover A

/-- The pointwise form: `A` lies in the essential image of the coherent
covers. -/
def S1871EssSurjAt (A : S1728Cover) : Prop :=
  ∃ C : CoherentCover, S1871CoverIso C.cover A

/-- Data-level form of an isomorphism of covers: a pair of cover maps whose two
composites are 2-isomorphic to the identities.  This is the form in which an
isomorphism is constructed or refuted. -/
def S1871RelIso (A B : S1728Cover) : Prop :=
  ∃ (f : S1728CoverMap A B) (g : S1728CoverMap B A),
    Nonempty (Iso (S1641CoverMapComp f g).map (S1641CoverMapId A).map) ∧
      Nonempty (Iso (S1641CoverMapComp g f).map (S1641CoverMapId B).map)

/-- **The data-level form is exactly the categorical isomorphism.**  Equality of
2-isomorphism classes is turned into a 2-isomorphism of the underlying strong
transformations by `S1832RelOfQuotEq`; conversely `Quot.sound` promotes a pair
of 2-isomorphic composites to an `Iso` of the quotient category. -/
theorem S1871RelIso_iff_iso (A B : S1728Cover) :
    S1871RelIso A B ↔ S1871CoverIso A B := by
  constructor
  · rintro ⟨f, g, ⟨ef⟩, ⟨eg⟩⟩
    refine ⟨{
      hom := S1832Q f
      inv := S1832Q g
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩
    · rw [S1832QuotComp]
      exact Quot.sound ⟨ef⟩
    · rw [S1832QuotComp]
      exact Quot.sound ⟨eg⟩
  · rintro ⟨e⟩
    refine ⟨Quot.out e.hom, Quot.out e.inv, ?_, ?_⟩
    · have h : e.hom ≫ e.inv = 𝟙 A := e.hom_inv_id
      rw [show e.hom = S1832Q (Quot.out e.hom) from (Quot.out_eq e.hom).symm,
        show e.inv = S1832Q (Quot.out e.inv) from (Quot.out_eq e.inv).symm,
        S1832QuotComp] at h
      exact S1832RelOfQuotEq h
    · have h : e.inv ≫ e.hom = 𝟙 B := e.inv_hom_id
      rw [show e.inv = S1832Q (Quot.out e.inv) from (Quot.out_eq e.inv).symm,
        show e.hom = S1832Q (Quot.out e.hom) from (Quot.out_eq e.hom).symm,
        S1832QuotComp] at h
      exact S1832RelOfQuotEq h

/-- The essential-surjectivity statement is literally Mathlib's
`Functor.EssSurj` of the S1854 forgetful functor. -/
theorem S1871EssSurj_iff_forget_essSurj :
    S1871EssSurj ↔ S1854Forget11.EssSurj := by
  constructor
  · intro h
    exact ⟨fun A => h A⟩
  · intro h A
    exact h.mem_essImage A

/-! ## 2. Covers with the same source and 2-isomorphic structure maps

The finite-etale datum of a cover is *object-level* data and is invisible to the
2-isomorphism category: a cover map only records a strong transformation between
the source stacks together with its comparison 2-cell to the target structure
map.  Consequently two covers with the same source and 2-isomorphic structure
maps are isomorphic, with the identity cover maps as the two directions.  This
is the observation that kills S1850's doubled cover as a candidate
counterexample. -/

/-- The identity cover map between two covers with the same source stack whose
structure maps are related by `e`: the structure map `f'` is pulled back to `f` by
the unitor and `e`. -/
noncomputable def S1871CoverMapOfIso (S : EtaleStackOverField S1726K)
    (f f' : S.Hom S1726Orbicurve.stack)
    (m : EtaleStackFiniteEtaleMorphism f) (m' : EtaleStackFiniteEtaleMorphism f')
    (e : Iso f f') :
    S1728CoverMap (OrbicurveFiniteEtaleCover.mk S f m)
      (OrbicurveFiniteEtaleCover.mk S f' m') where
  map := Pseudofunctor.StrongTrans.id S.fiber
  commutes := (S1756LeftUnitorIso f').trans e.symm

/-- The backward identity cover map, in the reverse direction. -/
noncomputable def S1871CoverMapOfIsoSymm (S : EtaleStackOverField S1726K)
    (f f' : S.Hom S1726Orbicurve.stack)
    (m : EtaleStackFiniteEtaleMorphism f) (m' : EtaleStackFiniteEtaleMorphism f')
    (e : Iso f f') :
    S1728CoverMap (OrbicurveFiniteEtaleCover.mk S f' m')
      (OrbicurveFiniteEtaleCover.mk S f m) where
  map := Pseudofunctor.StrongTrans.id S.fiber
  commutes := (S1756LeftUnitorIso f).trans e

/-- **The workhorse.**  Two covers with the same source stack and 2-isomorphic
structure maps are isomorphic in the S1728 2-isomorphism category, whatever
their finite-etale data.  The two identity cover maps are inverse up to
2-isomorphism by the bicategorical unitors. -/
theorem S1871IsoOfMapIso (S : EtaleStackOverField S1726K)
    (f f' : S.Hom S1726Orbicurve.stack)
    (m : EtaleStackFiniteEtaleMorphism f) (m' : EtaleStackFiniteEtaleMorphism f')
    (e : Iso f f') :
    Nonempty ((OrbicurveFiniteEtaleCover.mk S f m) ≅
      (OrbicurveFiniteEtaleCover.mk S f' m')) := by
  refine ⟨{
    hom := S1832Q (S1871CoverMapOfIso S f f' m m' e)
    inv := S1832Q (S1871CoverMapOfIsoSymm S f f' m m' e)
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩
  · rw [S1832QuotComp]
    exact Quot.sound ⟨S1756LeftUnitorIso (Pseudofunctor.StrongTrans.id S.fiber)⟩
  · rw [S1832QuotComp]
    exact Quot.sound ⟨S1756LeftUnitorIso (Pseudofunctor.StrongTrans.id S.fiber)⟩

/-- The special case of *literally* the same source and structure map. -/
theorem S1871IsoOfMk (S : EtaleStackOverField S1726K)
    (f : S.Hom S1726Orbicurve.stack)
    (m₁ m₂ : EtaleStackFiniteEtaleMorphism f) :
    Nonempty ((OrbicurveFiniteEtaleCover.mk S f m₁) ≅
      (OrbicurveFiniteEtaleCover.mk S f m₂)) :=
  S1871IsoOfMapIso S f f m₁ m₂ (Iso.refl f)

/-- **The doubled cover of S1850 is isomorphic to the coherent terminal cover.**
Both have the source stack of the orbicurve and the identity structure map; only
the finite-etale datum differs, and the 2-isomorphism category does not see that
datum.  This is the direct refutation of the candidate counterexample. -/
theorem S1871DoubledIsoTerminalCoherent :
    Nonempty (S1850DoubledCover ≅ S1852TerminalCoherent.cover) :=
  S1871IsoOfMk S1726Orbicurve.stack
    (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber)
    S1850DoubledFiniteEtale S1852IdStrong.toWeak

/-- **S1850's doubled cover is not a counterexample** to essential
surjectivity: it is isomorphic to a coherent cover.  S1852's
`S1852DoubledCover_not_coherent` only excludes *equality* of the underlying
cover, which is strictly stronger. -/
theorem S1871DoubledCover_not_counterexample :
    S1871EssSurjAt S1850DoubledCover := by
  obtain ⟨e⟩ := S1871DoubledIsoTerminalCoherent
  exact ⟨S1852TerminalCoherent, ⟨e.symm⟩⟩

/-- Every cover with the source of the orbicurve stack and the identity
structure map lies in the essential image of the coherent covers, whatever its
finite-etale datum: the whole identity class is covered. -/
theorem S1871IdentityCover_essSurjAt
    (m : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber)) :
    S1871EssSurjAt
      (OrbicurveFiniteEtaleCover.mk S1726Orbicurve.stack
        (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber) m) := by
  obtain ⟨e⟩ := S1871IsoOfMk S1726Orbicurve.stack
    (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber) m S1852IdStrong.toWeak
  exact ⟨S1852TerminalCoherent, ⟨e.symm⟩⟩

/-- **The equality version fails.**  Not every weak cover is *literally* the
underlying cover of a coherent cover; this is S1852's refutation of S1756's
first missing statement transported through `S1852FirstMissing_of_coherentAll`. -/
theorem S1871NotForallCoherentEq :
    ¬ (∀ A : S1728Cover, ∃ C : CoherentCover, C.cover = A) :=
  fun h => S1852NotFirstMissing
    ((S1852FirstMissing_iff_S1756).mpr (S1852FirstMissing_of_coherentAll h))

/-- The equality version would imply essential surjectivity, so the iso version
is strictly weaker. -/
theorem S1871EssSurj_of_forallEq
    (h : ∀ A : S1728Cover, ∃ C : CoherentCover, C.cover = A) : S1871EssSurj := by
  intro A
  obtain ⟨C, hC⟩ := h A
  refine ⟨C, ?_⟩
  rw [hC]
  exact ⟨Iso.refl A⟩

/-! ## 3. The unit 2-cell is not an invariant of the 2-isomorphism class

The doubled cover carries no unit 2-cell (`S1850NoUnit`), the terminal coherent
cover does, and the two are isomorphic.  Hence the unit is not an invariant of
the isomorphism class, and the unit-based refutation of essential surjectivity is
blocked at exactly this transfer step. -/

/-- **`S1756Unit` is not invariant under isomorphism of covers.** -/
theorem S1871Unit_not_iso_invariant :
    ∃ A B : S1728Cover, S1871CoverIso A B ∧ S1756Unit B ∧ ¬ S1756Unit A :=
  ⟨S1850DoubledCover, S1852TerminalCoherent.cover,
    S1871DoubledIsoTerminalCoherent, S1852TerminalCoherent.unit, S1850NoUnit⟩

/-- Consequently the unit 2-cell cannot be transported along an isomorphism of
covers: the transfer principle is false. -/
theorem S1871NotUnitTransfer :
    ¬ (∀ A B : S1728Cover, S1871CoverIso A B → S1756Unit A → S1756Unit B) := by
  intro h
  obtain ⟨A, B, hAB, hB, hA⟩ := S1871Unit_not_iso_invariant
  obtain ⟨e⟩ := hAB
  exact hA (h B A ⟨e.symm⟩ hB)

/-- **The blocked refutation of essential surjectivity.**  If the unit 2-cell
were an isomorphism invariant, essential surjectivity would imply S1756's first
missing statement.  That statement is false (S1850), and the transfer step is
false as well (`S1871NotUnitTransfer`); hence the doubled cover refutes the
transfer, not essential surjectivity. -/
theorem S1871FirstMissing_of_essSurj_of_unitTransfer
    (h : S1871EssSurj)
    (htr : ∀ A B : S1728Cover, S1871CoverIso A B → S1756Unit A → S1756Unit B) :
    S1756FirstMissing := by
  intro A
  obtain ⟨C, ⟨e⟩⟩ := h A
  exact (S1756Unit_iff_end A).mp (htr C.cover A ⟨e⟩ C.unit)

/-! ## 4. Strong realisation: the positive direction and the exact gap -/

/-- **Strong realisation on the slice, pointwise.**  The structure map of the
weak cover `A` is 2-isomorphic to a map, with the same source, that carries a
strong finite-etale structure.  This is the exact missing input for essential
surjectivity. -/
def S1871StrongInSliceAt (A : S1728Cover) : Prop :=
  ∃ f' : A.source.Hom S1726Orbicurve.stack,
    Nonempty (StrongEtaleStackFiniteEtaleMorphism f') ∧ Nonempty (Iso f' A.map)

/-- The global strong-realisation statement. -/
def S1871StrongInSlice : Prop := ∀ A : S1728Cover, S1871StrongInSliceAt A

/-- Strong realisation on the nose: the given structure map itself carries a
strong finite-etale structure. -/
def S1871StrongRealization : Prop :=
  ∀ A : S1728Cover, Nonempty (StrongEtaleStackFiniteEtaleMorphism A.map)

/-- On-the-nose strong realisation is a special case of realisation on the
slice. -/
theorem S1871StrongInSlice_of_strongRealization (h : S1871StrongRealization) :
    S1871StrongInSlice := by
  intro A
  obtain ⟨M⟩ := h A
  exact ⟨A.map, ⟨M⟩, ⟨Iso.refl A.map⟩⟩

/-- **The positive direction, pointwise.**  If the structure map of `A` is
2-isomorphic to a strongly finite-etale map with the same source, then `A` is in
the essential image of the coherent covers.  The coherent cover is built from
the strong structure and the *given* source, and the isomorphism is the pair of
identity cover maps. -/
theorem S1871EssSurjAt_of_strongInSliceAt (A : S1728Cover)
    (h : S1871StrongInSliceAt A) : S1871EssSurjAt A := by
  obtain ⟨f', ⟨M⟩, ⟨e⟩⟩ := h
  refine ⟨CoherentCover.ofStrong
    { source := A.source, map := f', finiteEtale := M }, ?_⟩
  exact S1871IsoOfMapIso A.source f' A.map M.toWeak A.finiteEtale e

/-- **Essential surjectivity follows from strong realisation on the slice.** -/
theorem S1871EssSurj_of_strongInSlice (h : S1871StrongInSlice) : S1871EssSurj :=
  fun A => S1871EssSurjAt_of_strongInSliceAt A (h A)

/-- If the structure map itself carries a strong structure, the cover is in the
essential image. -/
theorem S1871EssSurjAt_of_strong (A : S1728Cover)
    (M : StrongEtaleStackFiniteEtaleMorphism A.map) : S1871EssSurjAt A :=
  S1871EssSurjAt_of_strongInSliceAt A ⟨A.map, ⟨M⟩, ⟨Iso.refl A.map⟩⟩

/-- Strong realisation on the slice holds for the identity class, in particular
for S1850's doubled cover and the terminal cover: the missing statement is
satisfiable and not vacuous. -/
theorem S1871StrongInSliceAt_identityCover
    (m : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber)) :
    S1871StrongInSliceAt
      (OrbicurveFiniteEtaleCover.mk S1726Orbicurve.stack
        (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber) m) :=
  ⟨Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber,
    ⟨S1852IdStrong⟩, ⟨Iso.refl _⟩⟩

/-- **The exact transport obligation** connecting essential surjectivity with
strong realisation on the nose: an isomorphism of a weak cover with a coherent
cover produces a strong structure on the *given* structure map.  This is not
proved here; it is the precise bicategorical transport obligation of the
reduction `S1871EssSurj_iff_strongRealization`. -/
def S1871StrongTransfer : Prop :=
  ∀ (A : S1728Cover) (C : CoherentCover),
    S1871CoverIso A C.cover → Nonempty (StrongEtaleStackFiniteEtaleMorphism A.map)

/-- **The reduction.**  Given the transport, essential surjectivity is exactly
strong realisation on the nose: no other input is needed. -/
theorem S1871EssSurj_iff_strongRealization (h : S1871StrongTransfer) :
    S1871EssSurj ↔ S1871StrongRealization := by
  constructor
  · intro hE A
    obtain ⟨C, ⟨e⟩⟩ := hE A
    exact h A C ⟨e.symm⟩
  · intro hS
    exact S1871EssSurj_of_strongInSlice
      (S1871StrongInSlice_of_strongRealization hS)

/-! ### The exact reformulation: slice realisation -/

/-- **Slice 2-equivalence with a strongly finite-etale map.**  The structure map
of `A` is 2-isomorphic, along an equivalence of the source stack, to a map that
carries a strong finite-etale structure.  Unlike `S1871StrongInSliceAt` the source
stack is allowed to change inside the 2-isomorphism class.  This is the exact
geometric content that the coherent covers add. -/
def S1871StrongSliceEquivAt (A : S1728Cover) : Prop :=
  ∃ (S' : EtaleStackOverField S1726K) (f' : S'.Hom S1726Orbicurve.stack)
    (φ : Pseudofunctor.StrongTrans A.source.fiber S'.fiber)
    (ψ : Pseudofunctor.StrongTrans S'.fiber A.source.fiber),
    Nonempty (StrongEtaleStackFiniteEtaleMorphism f') ∧
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp φ ψ)
        (Pseudofunctor.StrongTrans.id A.source.fiber)) ∧
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp ψ φ)
        (Pseudofunctor.StrongTrans.id S'.fiber)) ∧
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp φ f') A.map)

/-- The global slice-realisation statement. -/
def S1871StrongSliceEquiv : Prop := ∀ A : S1728Cover, S1871StrongSliceEquivAt A

/-- The forward cover map of a slice equivalence. -/
noncomputable def S1871CoverMapOfSliceForward (A : S1728Cover)
    (S' : EtaleStackOverField S1726K) (f' : S'.Hom S1726Orbicurve.stack)
    (M : StrongEtaleStackFiniteEtaleMorphism f')
    (φ : Pseudofunctor.StrongTrans A.source.fiber S'.fiber)
    (e : Iso (Pseudofunctor.StrongTrans.vcomp φ f') A.map) :
    S1728CoverMap A (OrbicurveFiniteEtaleCover.mk S' f' M.toWeak) where
  map := φ
  commutes := e

/-- The backward cover map of a slice equivalence. -/
noncomputable def S1871CoverMapOfSliceBackward (A : S1728Cover)
    (S' : EtaleStackOverField S1726K) (f' : S'.Hom S1726Orbicurve.stack)
    (M : StrongEtaleStackFiniteEtaleMorphism f')
    (ψ : Pseudofunctor.StrongTrans S'.fiber A.source.fiber)
    (e : Iso (Pseudofunctor.StrongTrans.vcomp ψ A.map) f') :
    S1728CoverMap (OrbicurveFiniteEtaleCover.mk S' f' M.toWeak) A where
  map := ψ
  commutes := e

/-- The cover isomorphism built from slice data: the two cover maps of the
2-equivalence of source stacks, with the comparison 2-cell of the backward map
obtained from the forward comparison by cancelling the 2-equivalence. -/
theorem S1871IsoOfSliceData (A : S1728Cover)
    (S' : EtaleStackOverField S1726K) (f' : S'.Hom S1726Orbicurve.stack)
    (M : StrongEtaleStackFiniteEtaleMorphism f')
    (φ : Pseudofunctor.StrongTrans A.source.fiber S'.fiber)
    (ψ : Pseudofunctor.StrongTrans S'.fiber A.source.fiber)
    (hu1 : Iso (Pseudofunctor.StrongTrans.vcomp φ ψ)
      (Pseudofunctor.StrongTrans.id A.source.fiber))
    (hu2 : Iso (Pseudofunctor.StrongTrans.vcomp ψ φ)
      (Pseudofunctor.StrongTrans.id S'.fiber))
    (e : Iso (Pseudofunctor.StrongTrans.vcomp φ f') A.map) :
    Nonempty ((OrbicurveFiniteEtaleCover.mk S' f' M.toWeak) ≅ A) := by
  have h1 : Iso (Pseudofunctor.StrongTrans.vcomp ψ
      (Pseudofunctor.StrongTrans.vcomp φ f'))
      (Pseudofunctor.StrongTrans.vcomp ψ A.map) :=
    S1756WhiskerLeftIso ψ (Pseudofunctor.StrongTrans.vcomp φ f') A.map e
  have h2 : Iso (Pseudofunctor.StrongTrans.vcomp ψ
      (Pseudofunctor.StrongTrans.vcomp φ f')) f' :=
    (S1756AssociatorIso ψ φ f').symm.trans
      ((S1756WhiskerRightIso (Pseudofunctor.StrongTrans.vcomp ψ φ)
        (Pseudofunctor.StrongTrans.id S'.fiber) f' hu2).trans
        (S1756LeftUnitorIso f'))
  have h3 : Iso (Pseudofunctor.StrongTrans.vcomp ψ A.map) f' := h1.symm.trans h2
  refine ⟨{
    hom := S1832Q (S1871CoverMapOfSliceBackward A S' f' M ψ h3)
    inv := S1832Q (S1871CoverMapOfSliceForward A S' f' M φ e)
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩
  · rw [S1832QuotComp]
    exact Quot.sound ⟨hu2⟩
  · rw [S1832QuotComp]
    exact Quot.sound ⟨hu1⟩

/-- **Slice realisation gives essential surjectivity.**  The coherent cover is
built from the strong structure, and the cover isomorphism is
`S1871IsoOfSliceData`. -/
theorem S1871EssSurjAt_of_strongSliceEquivAt (A : S1728Cover)
    (h : S1871StrongSliceEquivAt A) : S1871EssSurjAt A := by
  obtain ⟨S', f', φ, ψ, ⟨M⟩, ⟨hu1⟩, ⟨hu2⟩, ⟨e⟩⟩ := h
  refine ⟨CoherentCover.ofStrong
    { source := S', map := f', finiteEtale := M }, ?_⟩
  exact S1871IsoOfSliceData A S' f' M φ ψ hu1 hu2 e

/-- Essential surjectivity follows from the global slice-realisation statement. -/
theorem S1871EssSurj_of_strongSliceEquiv (h : S1871StrongSliceEquiv) : S1871EssSurj :=
  fun A => S1871EssSurjAt_of_strongSliceEquivAt A (h A)

/-- **The converse direction of the exact reformulation**: a coherent cover
isomorphic to `A` produces a slice 2-equivalence of `A`'s structure map with
the coherent cover's strongly finite-etale map.  The 2-equivalence of source
stacks is read off from the two cover maps of the isomorphism. -/
theorem S1871StrongSliceEquivAt_of_essSurjAt (A : S1728Cover)
    (h : S1871EssSurjAt A) : S1871StrongSliceEquivAt A := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨f, g, ⟨hu1⟩, ⟨hu2⟩⟩ := (S1871RelIso_iff_iso C.cover A).mpr hC
  exact ⟨C.source, C.map, g.map, f.map, ⟨C.toStrongCover.finiteEtale⟩,
    ⟨hu2⟩, ⟨hu1⟩, ⟨g.commutes⟩⟩

/-- **Essential surjectivity is exactly slice realisation.**  This is the exact
form of the question: the coherent subcategory of the S1728 2-isomorphism
category is essentially surjective if and only if every weak cover's structure
map is 2-isomorphic, along an equivalence of its source stack, to a strongly
finite-etale map.  No other input enters. -/
theorem S1871EssSurj_iff_strongSliceEquiv :
    S1871EssSurj ↔ S1871StrongSliceEquiv := by
  constructor
  · intro h A
    exact S1871StrongSliceEquivAt_of_essSurjAt A (h A)
  · intro h
    exact S1871EssSurj_of_strongSliceEquiv h

/-- **The pointwise exact reformulation.** -/
theorem S1871EssSurjAt_iff_strongSliceEquivAt (A : S1728Cover) :
    S1871EssSurjAt A ↔ S1871StrongSliceEquivAt A :=
  ⟨S1871StrongSliceEquivAt_of_essSurjAt A, S1871EssSurjAt_of_strongSliceEquivAt A⟩

/-- Strong realisation on the nose suffices for essential surjectivity. -/
theorem S1871EssSurj_of_strongRealization (h : S1871StrongRealization) : S1871EssSurj :=
  S1871EssSurj_of_strongInSlice (S1871StrongInSlice_of_strongRealization h)

/-- Realisation with the source fixed is a special case of slice realisation. -/
theorem S1871StrongSliceEquivAt_of_strongInSliceAt (A : S1728Cover)
    (h : S1871StrongInSliceAt A) : S1871StrongSliceEquivAt A := by
  obtain ⟨f', ⟨M⟩, ⟨e⟩⟩ := h
  exact ⟨A.source, f', Pseudofunctor.StrongTrans.id A.source.fiber,
    Pseudofunctor.StrongTrans.id A.source.fiber, ⟨M⟩,
    ⟨S1756LeftUnitorIso (Pseudofunctor.StrongTrans.id A.source.fiber)⟩,
    ⟨S1756LeftUnitorIso (Pseudofunctor.StrongTrans.id A.source.fiber)⟩,
    ⟨(S1756LeftUnitorIso f').trans e⟩⟩

/-- The global form of the previous statement. -/
theorem S1871StrongSliceEquiv_of_strongInSlice (h : S1871StrongInSlice) :
    S1871StrongSliceEquiv :=
  fun A => S1871StrongSliceEquivAt_of_strongInSliceAt A (h A)

/-- The identity map of the orbicurve stack carries a strong finite-etale
structure: the unconditional strong-realisation instance available in the tree. -/
theorem S1871StrongRealizationAt_identity :
    Nonempty (StrongEtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber)) :=
  ⟨S1852IdStrong⟩

/-- Slice realisation holds at S1850's doubled cover: the candidate
counterexample even satisfies the exact first-missing statement. -/
theorem S1871StrongSliceEquivAt_doubled :
    S1871StrongSliceEquivAt S1850DoubledCover :=
  S1871StrongSliceEquivAt_of_strongInSliceAt _
    (S1871StrongInSliceAt_identityCover S1850DoubledFiniteEtale)

/-- Slice realisation holds at the terminal coherent cover. -/
theorem S1871StrongSliceEquivAt_terminal :
    S1871StrongSliceEquivAt S1852TerminalCoherent.cover :=
  S1871StrongSliceEquivAt_of_strongInSliceAt _
    (S1871StrongInSliceAt_identityCover S1852IdStrong.toWeak)

/-- **The diagnosis, in one statement.**  The doubled cover satisfies essential
surjectivity (it is isomorphic to the coherent terminal cover) although it has
no unit 2-cell; the equality version fails; and essential surjectivity follows
from strong realisation on the slice. -/
theorem S1871Diagnosis :
    S1871EssSurjAt S1850DoubledCover ∧
      ¬ S1756Unit S1850DoubledCover ∧
      S1756Unit S1852TerminalCoherent.cover ∧
      (¬ (∀ A : S1728Cover, ∃ C : CoherentCover, C.cover = A)) ∧
      (S1871StrongInSlice → S1871EssSurj) ∧
      (S1871EssSurj ↔ S1871StrongSliceEquiv) :=
  ⟨S1871DoubledCover_not_counterexample, S1850NoUnit,
    S1852TerminalCoherent.unit, S1871NotForallCoherentEq,
    S1871EssSurj_of_strongInSlice, S1871EssSurj_iff_strongSliceEquiv⟩

/-! ## 5. Checks -/

#check S1871CoverIso
#check S1871EssSurj
#check S1871EssSurjAt
#check S1871RelIso
#check S1871RelIso_iff_iso
#check S1871EssSurj_iff_forget_essSurj
#check S1871IsoOfMapIso
#check S1871IsoOfMk
#check S1871DoubledIsoTerminalCoherent
#check S1871DoubledCover_not_counterexample
#check S1871IdentityCover_essSurjAt
#check S1871NotForallCoherentEq
#check S1871EssSurj_of_forallEq
#check S1871Unit_not_iso_invariant
#check S1871NotUnitTransfer
#check S1871FirstMissing_of_essSurj_of_unitTransfer
#check S1871StrongInSliceAt
#check S1871StrongInSlice
#check S1871StrongRealization
#check S1871StrongTransfer
#check S1871StrongInSlice_of_strongRealization
#check S1871EssSurjAt_of_strongInSliceAt
#check S1871EssSurj_of_strongInSlice
#check S1871EssSurjAt_of_strong
#check S1871StrongInSliceAt_identityCover
#check S1871EssSurj_iff_strongRealization
#check S1871CoverMapOfIso
#check S1871CoverMapOfIsoSymm
#check S1871StrongSliceEquivAt
#check S1871StrongSliceEquiv
#check S1871CoverMapOfSliceForward
#check S1871CoverMapOfSliceBackward
#check S1871IsoOfSliceData
#check S1871EssSurjAt_of_strongSliceEquivAt
#check S1871EssSurj_of_strongSliceEquiv
#check S1871StrongSliceEquivAt_of_essSurjAt
#check S1871EssSurj_iff_strongSliceEquiv
#check S1871StrongSliceEquivAt_of_strongInSliceAt
#check S1871StrongSliceEquiv_of_strongInSlice
#check S1871EssSurjAt_iff_strongSliceEquivAt
#check S1871EssSurj_of_strongRealization
#check S1871StrongRealizationAt_identity
#check S1871StrongSliceEquivAt_doubled
#check S1871StrongSliceEquivAt_terminal
#check S1871Diagnosis

/-! ## 6. Axiom audit -/

#print axioms S1871RelIso_iff_iso
#print axioms S1871EssSurj_iff_forget_essSurj
#print axioms S1871IsoOfMapIso
#print axioms S1871IsoOfMk
#print axioms S1871DoubledIsoTerminalCoherent
#print axioms S1871DoubledCover_not_counterexample
#print axioms S1871IdentityCover_essSurjAt
#print axioms S1871NotForallCoherentEq
#print axioms S1871EssSurj_of_forallEq
#print axioms S1871Unit_not_iso_invariant
#print axioms S1871NotUnitTransfer
#print axioms S1871FirstMissing_of_essSurj_of_unitTransfer
#print axioms S1871StrongInSlice_of_strongRealization
#print axioms S1871EssSurjAt_of_strongInSliceAt
#print axioms S1871EssSurj_of_strongInSlice
#print axioms S1871EssSurjAt_of_strong
#print axioms S1871StrongInSliceAt_identityCover
#print axioms S1871EssSurj_iff_strongRealization
#print axioms S1871CoverMapOfIso
#print axioms S1871CoverMapOfIsoSymm
#print axioms S1871CoverMapOfSliceForward
#print axioms S1871CoverMapOfSliceBackward
#print axioms S1871IsoOfSliceData
#print axioms S1871EssSurjAt_of_strongSliceEquivAt
#print axioms S1871EssSurj_of_strongSliceEquiv
#print axioms S1871StrongSliceEquivAt_of_essSurjAt
#print axioms S1871EssSurj_iff_strongSliceEquiv
#print axioms S1871StrongSliceEquivAt_of_strongInSliceAt
#print axioms S1871StrongSliceEquiv_of_strongInSlice
#print axioms S1871EssSurjAt_iff_strongSliceEquivAt
#print axioms S1871EssSurj_of_strongRealization
#print axioms S1871StrongSliceEquivAt_doubled
#print axioms S1871StrongSliceEquivAt_terminal
#print axioms S1871Diagnosis

end LeanFormal.IUT.XiFPaper.S1871CoherentEssSurjActual