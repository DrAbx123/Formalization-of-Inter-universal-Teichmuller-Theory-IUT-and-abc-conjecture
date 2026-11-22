/-
# S1854: the actual category of coherent (strong) covers, and the transports

S1852 built the coherent cover datum

    CoherentCover  =  StrongCover  +  the S1756 unit 2-cell at the identity point,

where StrongCover records a strong finite-etale structure on the structure map (every
base-change presentation carries the full 2-universal property S1852ConeEssSurj), and
proved that S1756's first missing statement holds for every coherent cover.  S1852
explicitly left open: no category structure on the coherent covers is constructed.
This file constructs it, proves the forgetful functor full and faithful on
2-isomorphism classes, and transports the available structure to the coherent
subcategory, naming the exact first missing for the rest.

## What is built here

1. S1854Compatible: the compatibility predicate on S1728 cover maps between coherent
   covers.  A cover map f : A.cover -> B.cover is compatible when it is compatible with
   the identity-point base-change comparison of the two coherent covers:

     exists g : model A -> model B,   f vcomp lift_B  =  lift_A vcomp g
   (up to 2-isomorphism), where lift_A, lift_B are the unconditional lifts of the
   identity-point two-pullbacks of the two covers (S1743Lift), i.e. exactly the
   comparison 1-cells attached to the recorded cover, hence to the coherent datum.

2. S1854Compatible_of_map: EVERY S1728 cover map between coherent covers is
   compatible.  The proof uses only the unconditional counit of the identity-point
   two-pullback (lift vcomp toSource = 1) and the bicategorical unitors.  Hence the
   forgetful map on 2-isomorphism classes of compatible maps is bijective, and the
   coherent category is the FULL subcategory of the S1728 2-isomorphism category at
   the level of the underlying covers: compatibility constrains nothing on the homs.
   This is proved, not assumed, so the full/faithful statement is not vacuous.

3. S1854CoherentMap / S1854CoherentQuot / S1854QuotEquiv: the compatible cover maps,
   their 2-isomorphism quotient, and the bijection of that quotient with the S1728
   2-isomorphism classes of the underlying cover maps.

4. S1854CoherentCategory11 : Category.{1,1} CoherentCover, whose homs are the
   2-isomorphism classes of compatible cover maps.  It is obtained by transporting the
   S1728 2-isomorphism quotient category (S1728ActualCategory11) along the hom
   bijection, using the object-map-generalised transport lemma
   S1854CategoryOfHomEquivOn (the generalisation of S1728CategoryOfHomEquiv to a
   different object type with a forgetful object map).  No axiom, no placeholder:
   id and comp are the transported S1728 ones and the three laws are proved by
   injectivity of the hom bijection.

5. S1854Forget11 : CoherentCover -> S1728Cover, the forgetful functor to
   S1728ActualCategory11.  Instances S1854Forget11.Full and S1854Forget11.Faithful
   are proved, together with S1854Forget11_map_bijective: the induced map on
   2-isomorphism classes of cover maps is bijective.

6. S1854CoherentCategory01 : Category.{0,1} CoherentCover, the same category at the
   target hom universe, with homs the S1766 Type-0 small carrier
   S1766QuotSmallCarrier of the underlying covers; and S1854Forget01, full and
   faithful to S1809's actual Category.{0,1} S1809CoverCategory01 on the cover type.

7. Transports:
   * the terminal object: S1854TerminalCoherent is a coherent cover whose underlying
     cover is literally S1762's terminal cover, and it is terminal in the coherent
     category at both hom universes (S1854TerminalCoherent_isTerminal,
     S1854HasTerminal, S1854TerminalCoherent01_isTerminal, S1854HasTerminal01);
   * S1828's R1: the slice model category is transported to the coherent covers
     (S1854ModelSliceCategory), the forgetful functor to S1828ModelOverCategory is
     full and faithful, and the coherent strict hom realisation S1854CoherentR1 is
     proved from the same two hypotheses as S1828 (S1755SourceRetraction,
     S1766CoverMapDiscrete) in S1854CoherentR1_modelSlice;
   * pullbacks and finite coproducts: the exact remaining input is named
     (S1854PullbackApexCoherent, S1854CoproductApexCoherent: the pullback, resp.
     initial/binary-coproduct cover of coherent covers must again be coherent) and
     the transport statements are recorded as the named propositions
     S1854PullbackTransport and S1854CoproductTransport.  They are NOT proved here
     and no inhabitant is asserted.

## Honest boundary

* The compatibility predicate is automatic (item 2): the coherent structure restricts
  the objects, not the homs.  The coherent category is thus the full subcategory of the
  S1728 2-isomorphism category on the coherent covers, and this is a theorem.
* No existing definition is modified: S1852's CoherentCover, StrongCover,
  S1852ConeEssSurj and S1728's Category.{1,1} are untouched.
* The transport of the terminal object and of S1828's R1 is unconditional given the
  hypotheses S1828 already uses.  The pullback/coproduct transports are recorded as
  the exact remaining input and are not proved.
* No sorry, no axiom, no fake category.  Only propext, Classical.choice and Quot.sound;
  see the audit block.
-/

import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1809SmallCarrierCategoryActual
import tmp.sheaf.xif.paper.S1828SliceR1Actual
import tmp.sheaf.xif.paper.S1762CoverLimitsActual
import tmp.sheaf.xif.paper.S1833ActualCoverCoproductsActual
import tmp.sheaf.xif.paper.S1832ActualCoverPullbacksActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut

universe u v w x

open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1766CanonicalModelInjectivityActual
open LeanFormal.IUT.XiFPaper.S1809SmallCarrierCategoryActual
open LeanFormal.IUT.XiFPaper.S1812InverseModelHomActual
open LeanFormal.IUT.XiFPaper.S1828SliceR1Actual
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual

/-! ## 1. Compatible cover maps -/

/-- Explicitly parametrised vertical composition of strong transformations.  The four
object parameters are given explicitly so that elaboration with an expected type does
not force the wrong middle object. -/
noncomputable abbrev S1854Vcomp {A B C : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C) :
    Pseudofunctor.StrongTrans A C :=
  Pseudofunctor.StrongTrans.vcomp f g

/-- The affine model map attached to a cover map between coherent covers: the composite
of the unconditional identity-point comparison to the source of B and the lift of B. -/
noncomputable def S1854ModelMap {A B : CoherentCover}
    (f : S1728CoverMap A.cover B.cover) :
    Pseudofunctor.StrongTrans (S1743ModelStack A.cover) (S1743ModelStack B.cover) :=
  S1854Vcomp (S1756ToSource A.cover) (S1854Vcomp f.map (S1743Lift B.cover))

/-- **Compatibility of a cover map with the strong presentations.**  The cover map f is
carried by a map g of the affine models of the two coherent covers: f vcomp lift_B is
2-isomorphic to lift_A vcomp g.  This is the naturality of the identity-point
base-change comparison of the coherent datum along f. -/
def S1854Compatible {A B : CoherentCover}
    (f : S1728CoverMap A.cover B.cover) : Prop :=
  exists g : Pseudofunctor.StrongTrans (S1743ModelStack A.cover) (S1743ModelStack B.cover),
    Nonempty (Iso (S1854Vcomp f.map (S1743Lift B.cover))
      (S1854Vcomp (S1743Lift A.cover) g))

/-- The unconditional counit of the identity-point two-pullback of a cover:
lift vcomp toSource is 2-isomorphic to the identity. -/
noncomputable def S1854Counit (A : CoherentCover) :
    Iso (S1854Vcomp (S1743Lift A.cover) (S1756ToSource A.cover))
      (Pseudofunctor.StrongTrans.id (S1743Source A.cover)) :=
  (S1743BaseChange A.cover).isPullback.liftToX (S1743Source A.cover)
    (S1743IdentityCone A.cover)

/-- Compatibility depends only on the 2-isomorphism class of the cover map. -/
theorem S1854Compatible_of_rel {A B : CoherentCover}
    {f g : S1728CoverMap A.cover B.cover} (h : S1728CoverMapRel f g)
    (hf : S1854Compatible f) : S1854Compatible g := by
  obtain ⟨e⟩ := h
  obtain ⟨m, ⟨e2⟩⟩ := hf
  refine ⟨m, ⟨?_⟩⟩
  exact (S1756WhiskerRightIso g.map f.map (S1743Lift B.cover) e.symm).trans e2

/-- **Every cover map between coherent covers is compatible.**  The model map is
S1854ModelMap f, and the comparison 2-cell is obtained by cancelling the unconditional
counit lift vcomp toSource = 1 of the identity-point base change of A. -/
theorem S1854Compatible_of_map {A B : CoherentCover}
    (f : S1728CoverMap A.cover B.cover) : S1854Compatible f := by
  refine ⟨S1854ModelMap f, ⟨?_⟩⟩
  have h1 : Iso (S1854Vcomp f.map (S1743Lift B.cover))
      (S1854Vcomp (Pseudofunctor.StrongTrans.id (S1743Source A.cover))
        (S1854Vcomp f.map (S1743Lift B.cover))) :=
    (S1756LeftUnitorIso (S1854Vcomp f.map (S1743Lift B.cover))).symm
  have h2 : Iso
      (S1854Vcomp (Pseudofunctor.StrongTrans.id (S1743Source A.cover))
        (S1854Vcomp f.map (S1743Lift B.cover)))
      (S1854Vcomp (S1854Vcomp (S1743Lift A.cover) (S1756ToSource A.cover))
        (S1854Vcomp f.map (S1743Lift B.cover))) :=
    (S1756WhiskerRightIso (S1854Vcomp (S1743Lift A.cover) (S1756ToSource A.cover))
      (Pseudofunctor.StrongTrans.id (S1743Source A.cover))
      (S1854Vcomp f.map (S1743Lift B.cover)) (S1854Counit A)).symm
  have h3 : Iso
      (S1854Vcomp (S1854Vcomp (S1743Lift A.cover) (S1756ToSource A.cover))
        (S1854Vcomp f.map (S1743Lift B.cover)))
      (S1854Vcomp (S1743Lift A.cover)
        (S1854Vcomp (S1756ToSource A.cover)
          (S1854Vcomp f.map (S1743Lift B.cover)))) :=
    S1756AssociatorIso (S1743Lift A.cover) (S1756ToSource A.cover)
      (S1854Vcomp f.map (S1743Lift B.cover))
  exact h1.trans (h2.trans h3)

/-! ## 2. The 2-isomorphism quotient of compatible maps and its bijection with S1728 -/

/-- Compatible cover maps between coherent covers. -/
abbrev S1854CoherentMap (A B : CoherentCover) : Type 1 :=
  { f : S1728CoverMap A.cover B.cover // S1854Compatible f }

/-- The 2-isomorphism quotient of compatible cover maps. -/
abbrev S1854CoherentQuot (A B : CoherentCover) : Type 1 :=
  Quot (fun f g : S1854CoherentMap A B => Nonempty (Iso f.1.map g.1.map))

/-- The forgetful map from compatible-map classes to S1728 cover-map classes. -/
noncomputable def S1854QuotToCover {A B : CoherentCover} :
    S1854CoherentQuot A B → S1728CoverMapClass (A := A.cover) (B := B.cover) :=
  Quot.map (fun f : S1854CoherentMap A B => (f.1 : S1728CoverMap A.cover B.cover))
    (fun _ _ h => h)

/-- **The forgetful map on 2-isomorphism classes is surjective.**  A class of cover
maps is represented by any of its representatives, and every cover map is compatible. -/
theorem S1854QuotToCover_surjective {A B : CoherentCover} :
    Function.Surjective (S1854QuotToCover (A := A) (B := B)) := by
  intro q
  refine ⟨Quot.mk _ ⟨Quot.out q, S1854Compatible_of_map _⟩, ?_⟩
  exact Quot.out_eq q

/-- **The forgetful map on 2-isomorphism classes is injective.** -/
theorem S1854QuotToCover_injective {A B : CoherentCover} :
    Function.Injective (S1854QuotToCover (A := A) (B := B)) := by
  intro x y h
  induction x using Quot.inductionOn with
  | h f =>
    induction y using Quot.inductionOn with
    | h g =>
      apply Quot.sound
      exact S1809EqvGen_to_rel
        (S1728CoverMapRel_equivalence (A := A.cover) (B := B.cover))
        (Quot.eqvGen_exact h)

/-- The forgetful map as an equivalence of hom types. -/
noncomputable def S1854QuotEquiv (A B : CoherentCover) :
    S1854CoherentQuot A B ≃ S1728CoverMapClass (A := A.cover) (B := B.cover) :=
  Equiv.ofBijective _ ⟨S1854QuotToCover_injective, S1854QuotToCover_surjective⟩

/-! ## 3. The transported categories -/

/-- Transport a category structure along a family of equivalences of hom-types, for a
forgetful object map into an existing category.  This is S1728's
S1728CategoryOfHomEquiv with the object type and the object map separated, and with the
two hom universes independent.  The three category laws are proved by injectivity of
the hom equivalence; no strictness of the source 2-cells is required. -/
@[reducible] noncomputable def S1854CategoryOfHomEquivOn
    {D : Type u} [Category.{v, u} D]
    {E : Type w} (φ : E → D) (H : E → E → Type x)
    (e : forall A B, H A B ≃ (φ A ⟶ φ B)) : Category.{x, w} E where
  Hom := H
  id A := (e A A).symm (𝟙 (φ A))
  comp {A B C} f g := (e A C).symm ((e A B f) ≫ (e B C g))
  id_comp {A B} f := by
    apply (e A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.id_comp (f := e A B f)
  comp_id {A B} f := by
    apply (e A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.comp_id (f := e A B f)
  assoc {A B C Z} f g h := by
    apply (e A Z).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.assoc (f := e A B f) (g := e B C g) (h := e C Z h)

/-- **The actual category of coherent covers at the 2-isomorphism universe.**  Its homs
are the 2-isomorphism classes of compatible cover maps.  It is the transport of
S1728ActualCategory11 along the hom bijection S1854QuotEquiv. -/
@[reducible] noncomputable def S1854CoherentCategory11 : Category.{1, 1} CoherentCover :=
  S1854CategoryOfHomEquivOn (D := S1728Cover) (φ := CoherentCover.cover)
    (H := S1854CoherentQuot) (fun A B => S1854QuotEquiv A B)

/-- The hom types of the coherent category are literally the quotients of compatible
maps. -/
theorem S1854CoherentCategory11_hom (A B : CoherentCover) :
    (@Quiver.Hom _ S1854CoherentCategory11.toQuiver A B) = S1854CoherentQuot A B := rfl

/-! ## 4. The forgetful functor to the S1728 2-isomorphism category -/

section Coherent11

attribute [local instance] S1854CoherentCategory11

/-- The forgetful functor from the coherent category to the S1728 2-isomorphism
category of covers, on the underlying covers. -/
noncomputable def S1854Forget11 : CoherentCover ⥤ S1728Cover where
  obj A := A.cover
  map {A B} f := S1854QuotEquiv A B f
  map_id A := by exact Equiv.apply_symm_apply _ _
  map_comp {A B C} f g := by exact Equiv.apply_symm_apply _ _

/-- **The forgetful functor is full**: every S1728 cover-map class between two coherent
covers has a compatible representative (namely any representative, by
S1854Compatible_of_map). -/
instance S1854Forget11_full : S1854Forget11.Full where
  map_surjective {A B} f := ⟨(S1854QuotEquiv A B).symm f, Equiv.apply_symm_apply _ _⟩

/-- **The forgetful functor is faithful**. -/
instance S1854Forget11_faithful : S1854Forget11.Faithful where
  map_injective {A B} f g h := (S1854QuotEquiv A B).injective h

/-- **Full and faithful on 2-isomorphism classes**, stated as bijectivity of the
induced map on the hom types. -/
theorem S1854Forget11_map_bijective (A B : CoherentCover) :
    Function.Bijective (fun f : A ⟶ B => S1854Forget11.map f) :=
  ⟨fun f g h => (S1854QuotEquiv A B).injective h,
   fun f => ⟨(S1854QuotEquiv A B).symm f, Equiv.apply_symm_apply _ _⟩⟩

theorem S1854Forget11_full_statement : S1854Forget11.Full := inferInstance

theorem S1854Forget11_faithful_statement : S1854Forget11.Faithful := inferInstance

/-! ## 5. The terminal coherent cover -/

/-- The strong finite-etale structure on S1762's terminal (identity) cover, with exactly
the same weak base-change presentations.  The cone-comparison essential surjectivity is
S1852's S1852IdStrongBc, whose underlying presentation is literally S1762IdBaseChange. -/
noncomputable def S1854StrongOfS1762 :
    StrongEtaleStackFiniteEtaleMorphism S1762TerminalCover.map where
  baseChange T q :=
    ⟨S1762TerminalCover.finiteEtale.baseChange T q, (S1852IdStrongBc T q).coneEssSurj⟩
  hasProperty T q := S1762TerminalCover.finiteEtale.hasProperty T q

/-- The strong terminal cover. -/
noncomputable def S1854TerminalStrong : StrongCover S1726Orbicurve where
  source := S1762TerminalCover.source
  map := S1762TerminalCover.map
  finiteEtale := S1854StrongOfS1762

/-- The coherent terminal cover: the identity cover with its strong structure and the
unit 2-cell derived from the full 2-universal property. -/
noncomputable def S1854TerminalCoherent : CoherentCover where
  toStrongCover := S1854TerminalStrong
  unit := S1852Unit_of_strong S1854TerminalStrong

/-- Its underlying recorded cover is literally S1762's terminal cover. -/
theorem S1854TerminalCover_eq : S1854TerminalCoherent.cover = S1762TerminalCover := rfl

/-- Its underlying cover is terminal in the S1728 2-isomorphism category. -/
noncomputable def S1854TerminalCover_isTerminal :
    Limits.IsTerminal S1854TerminalCoherent.cover := by
  rw [S1854TerminalCover_eq]
  exact S1762TerminalCover_isTerminal

/-- The canonical morphism from a coherent cover to the terminal coherent cover. -/
noncomputable def S1854TerminalMap (A : CoherentCover) :
    A ⟶ S1854TerminalCoherent :=
  (S1854QuotEquiv A S1854TerminalCoherent).symm
    (S1854TerminalCover_isTerminal.from A.cover)

/-- It is the unique such morphism. -/
theorem S1854TerminalMap_unique (A : CoherentCover)
    (m : A ⟶ S1854TerminalCoherent) : m = S1854TerminalMap A := by
  have h : S1854QuotEquiv A S1854TerminalCoherent m
      = S1854TerminalCover_isTerminal.from A.cover :=
    S1854TerminalCover_isTerminal.hom_ext _ _
  calc m = (S1854QuotEquiv A S1854TerminalCoherent).symm
        (S1854QuotEquiv A S1854TerminalCoherent m) :=
        (Equiv.symm_apply_apply (S1854QuotEquiv A S1854TerminalCoherent) m).symm
    _ = S1854TerminalMap A :=
        congrArg (S1854QuotEquiv A S1854TerminalCoherent).symm h

/-- **The terminal coherent cover is terminal in the coherent category.**  This is the
first structure transported from S1762 to the coherent subcategory, unconditionally. -/
noncomputable def S1854TerminalCoherent_isTerminal :
    Limits.IsTerminal S1854TerminalCoherent :=
  Limits.IsTerminal.ofUniqueHom S1854TerminalMap S1854TerminalMap_unique

/-- **The coherent category has a terminal object** (S1762's terminal field,
transported). -/
theorem S1854HasTerminal : Limits.HasTerminal CoherentCover :=
  S1854TerminalCoherent_isTerminal.hasTerminal

/-- The affine model of the terminal coherent cover is the base scheme itself. -/
theorem S1854TerminalModel_eq :
    S1733Model S1854TerminalCoherent.cover = S1726AffineOver := rfl

/-- S1756's first missing statement on the terminal coherent cover. -/
theorem S1854TerminalEnd :
    S1756End S1854TerminalCoherent.cover = 𝟙 (S1733Model S1854TerminalCoherent.cover) :=
  S1852FirstMissingOnCoherent S1854TerminalCoherent

end Coherent11

/-! ## 6. R1 on the coherent covers: the general hom-realisation statement -/

section CoherentR1

variable [Category.{0, 1} CoherentCover]

/-- Hom-wise equivalences between the homs of a Category.{0,1} on the coherent covers
and the compatible cover maps, compatible with identities and composition up to
2-isomorphism.  This is S1754's S1754StrictHomEquiv at the coherent objects. -/
structure S1854CoherentStrictHomEquiv where
  /-- The hom-wise equivalences with the compatible cover maps. -/
  equiv : forall (A B : CoherentCover), (A ⟶ B) ≃ S1854CoherentMap A B
  /-- The identity is sent to the identity cover map up to 2-isomorphism. -/
  id_compat : forall (A : CoherentCover),
    Iso ((equiv A A (𝟙 A)).1.map) (Pseudofunctor.StrongTrans.id A.cover.source.fiber)
  /-- Composition is respected up to 2-isomorphism. -/
  comp_compat : forall {A B C : CoherentCover} (f : A ⟶ B) (g : B ⟶ C),
    Iso ((equiv A C (f ≫ g)).1.map)
      (Pseudofunctor.StrongTrans.vcomp ((equiv A B f).1.map) ((equiv B C g).1.map))

/-- **R1 on the coherent covers**: the coherent analogue of S1828's R1 statement. -/
def S1854CoherentR1 : Prop := Nonempty S1854CoherentStrictHomEquiv

end CoherentR1

/-! ## 7. The slice model category on the coherent covers, and R1 -/

section CoherentSlice

/-- The slice model category on the coherent covers: the objects are the coherent
covers, the homs are the slice model morphisms S1812ModelHomOver of the underlying
covers.  This is S1828's corrected model category S1828ModelOverCategory at the
coherent objects. -/
@[reducible] noncomputable def S1854ModelSliceCategory :
    Category.{0, 1} CoherentCover where
  Hom A B := S1812ModelHomOver A.cover B.cover
  id A := S1828SliceId A.cover
  comp f g := S1828SliceComp f g
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

/-- The forgetful functor from the coherent slice model category to S1828's slice model
category: the identity on objects and on the slice hom types. -/
noncomputable def S1854ModelSliceForget :
    @CategoryTheory.Functor CoherentCover S1854ModelSliceCategory S1728Cover
      S1828ModelOverCategory := by
  letI := S1854ModelSliceCategory
  letI := S1828ModelOverCategory
  exact { obj := fun A => A.cover
          map := fun {A B} f => f
          map_id := fun A => rfl
          map_comp := fun {A B C} f g => rfl }

attribute [local instance] S1854ModelSliceCategory S1828ModelOverCategory

/-- The forgetful functor of the slice model categories is full. -/
instance S1854ModelSliceForget_full : S1854ModelSliceForget.Full where
  map_surjective {A B} f := ⟨f, rfl⟩

/-- The forgetful functor of the slice model categories is faithful. -/
instance S1854ModelSliceForget_faithful : S1854ModelSliceForget.Faithful where
  map_injective {A B} f g h := h

/-- **Full and faithful on the slice hom types**: the induced map on homs is bijective. -/
theorem S1854ModelSliceForget_map_bijective (A B : CoherentCover) :
    Function.Bijective (fun f :
      @Quiver.Hom _ S1854ModelSliceCategory.toQuiver A B =>
      S1854ModelSliceForget.map f) :=
  ⟨fun f g h => h, fun f => ⟨f, rfl⟩⟩

/-- The slice model hom equivalence on the coherent covers, from S1828's equivalence
between slice model homs and actual cover maps. -/
noncomputable def S1854SliceHomEquiv (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) (A B : CoherentCover) :
    S1812ModelHomOver A.cover B.cover ≃ S1854CoherentMap A B where
  toFun g := ⟨(S1828SliceHomEquiv h hd A.cover B.cover) g, S1854Compatible_of_map _⟩
  invFun F := (S1828SliceHomEquiv h hd A.cover B.cover).symm F.1
  left_inv g := (S1828SliceHomEquiv h hd A.cover B.cover).left_inv g
  right_inv F := Subtype.ext ((S1828SliceHomEquiv h hd A.cover B.cover).right_inv F.1)

/-- **R1 for the coherent slice model category**, from the same two hypotheses as S1828
(the missing unit of the identity-point two-pullback, and discreteness of cover-map hom
types); the identity and composition compatibility laws are S1828's S1828ToCoverMap_id
and S1828ToCoverMap_comp at the underlying covers. -/
theorem S1854CoherentR1_modelSlice (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) : S1854CoherentR1 := by
  refine ⟨?_⟩
  refine ⟨fun A B => S1854SliceHomEquiv h hd A B, ?_, ?_⟩
  · intro A
    exact S1828ToCoverMap_id A.cover
  · intro A B C f g
    exact S1828ToCoverMap_comp h f g

end CoherentSlice

/-! ## 8. The exact remaining input for pullbacks and finite coproducts -/

/-- **The pullback-apex coherence condition** (under HasPullbacks of the S1728
2-isomorphism category): for every cospan of underlying covers of coherent covers, the
chosen S1728 pullback object is the underlying cover of some coherent cover.  This is
the geometric content that the strong presentation survives the pullback construction.
It is not proved here. -/
def S1854PullbackApexCoherent (h : Limits.HasPullbacks S1728Cover) : Prop := by
  letI := h
  exact forall (A B C : CoherentCover) (f : A.cover ⟶ C.cover) (g : B.cover ⟶ C.cover),
    Nonempty { P : CoherentCover // P.cover = Limits.pullback f g }

/-- **The coproduct-apex coherence condition**: the initial cover and the binary
coproduct covers of coherent covers are again coherent.  It is not proved here. -/
def S1854CoproductApexCoherent (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover) : Prop := by
  letI := h0
  letI := h2
  exact (Nonempty { P : CoherentCover // P.cover = (⊥_ S1728Cover) }) ∧
    (forall (A B : CoherentCover),
      Nonempty { P : CoherentCover // P.cover = (A.cover ⨿ B.cover) })

/-- **The pullback transport statement**: the S1728 pullback obligation together with
pullback-apex coherence gives pullbacks on the coherent category.  It is the exact
remaining categorical transport; it is recorded, not proved. -/
def S1854PullbackTransport : Prop :=
  forall (h : Limits.HasPullbacks S1728Cover), S1854PullbackApexCoherent h →
    @Limits.HasPullbacks CoherentCover S1854CoherentCategory11

/-- **The coproduct transport statement**: initial objects and binary coproducts on the
S1728 category, together with coproduct-apex coherence, give them on the coherent
category.  It is recorded, not proved. -/
def S1854CoproductTransport : Prop :=
  forall (h0 : Limits.HasInitial S1728Cover) (h2 : Limits.HasBinaryCoproducts S1728Cover),
    S1854CoproductApexCoherent h0 h2 →
      (@Limits.HasInitial CoherentCover S1854CoherentCategory11 ∧
        @Limits.HasBinaryCoproducts CoherentCover S1854CoherentCategory11)

/-- **The exact first missing for pullbacks on the coherent covers**, in S1832's terms:
S1832's bicategorical fibre-product input for the underlying covers, together with
pullback-apex coherence.  Recorded, not proved. -/
def S1854PullbackFirstMissing : Prop :=
  S1832FirstMissingPullback ∧ S1854PullbackTransport

/-- **The exact first missing for finite coproducts on the coherent covers**, in S1833's
terms: S1833's affine-comparison input, together with coproduct-apex coherence.
Recorded, not proved. -/
def S1854CoproductFirstMissing : Prop :=
  S1833FirstMissing ∧ S1854CoproductTransport

/-- The two exact first-missing statements together. -/
def S1854LimitsFirstMissing : Prop :=
  S1854PullbackFirstMissing ∧ S1854CoproductFirstMissing

/-! ## 9. The coherent category at the target hom universe -/

/-- The Type-0 small homs of the coherent category: the S1766 small carrier of the
underlying covers. -/
abbrev S1854SmallHom (A B : CoherentCover) : Type :=
  S1766QuotSmallCarrier A.cover B.cover

/-- The small homs are equivalent to the S1728 cover-map classes of the underlying
covers (S1766's unconditional equivalence). -/
noncomputable abbrev S1854SmallHomEquiv (A B : CoherentCover) :
    S1854SmallHom A B ≃ (A.cover ⟶ B.cover) :=
  (S1766QuotSmallEquiv A.cover B.cover).symm

/-- **The actual coherent cover category at the target universe**: Category.{0,1} on the
coherent covers, with homs the S1766 Type-0 small carrier of the underlying covers.
It is the transport of S1809's S1809CoverCategory01 along the forgetful object map,
exactly as S1809 is the transport of S1728's quotient category. -/
@[reducible] noncomputable def S1854CoherentCategory01 : Category.{0, 1} CoherentCover :=
  S1854CategoryOfHomEquivOn (D := S1728Cover) (φ := CoherentCover.cover)
    (H := S1854SmallHom) (fun A B => S1854SmallHomEquiv A B)

theorem S1854CoherentCategory01_hom (A B : CoherentCover) :
    (@Quiver.Hom _ S1854CoherentCategory01.toQuiver A B) = S1854SmallHom A B := rfl

section Coherent01

attribute [local instance] S1854CoherentCategory01 S1809CoverCategory01

/-- The forgetful functor from the coherent Category.{0,1} to S1809's actual
Category.{0,1} on the S1726 cover type: the identity on objects and on the small hom
carriers. -/
noncomputable def S1854Forget01 :
    @CategoryTheory.Functor CoherentCover S1854CoherentCategory01 S1728Cover
      S1809CoverCategory01 := by
  letI := S1854CoherentCategory01
  letI := S1809CoverCategory01
  exact { obj := fun A => A.cover
          map := fun {A B} f => f
          map_id := fun A => rfl
          map_comp := fun {A B C} f g => rfl }

/-- The forgetful functor at the target universe is full. -/
instance S1854Forget01_full : S1854Forget01.Full where
  map_surjective {A B} f := ⟨f, rfl⟩

/-- The forgetful functor at the target universe is faithful. -/
instance S1854Forget01_faithful : S1854Forget01.Faithful where
  map_injective {A B} f g h := h

/-- **Full and faithful at the target universe**, stated as bijectivity of the induced
map on the hom types. -/
theorem S1854Forget01_map_bijective (A B : CoherentCover) :
    Function.Bijective (fun f : A ⟶ B => S1854Forget01.map f) :=
  ⟨fun f g h => h, fun f => ⟨f, rfl⟩⟩

theorem S1854Forget01_full_statement : S1854Forget01.Full := inferInstance

theorem S1854Forget01_faithful_statement : S1854Forget01.Faithful := inferInstance

end Coherent01

section Coherent01Terminal

attribute [local instance] S1854CoherentCategory01

/-- The canonical morphism to the terminal coherent cover, at the target hom universe. -/
noncomputable def S1854TerminalMap01 (A : CoherentCover) :
    A ⟶ S1854TerminalCoherent :=
  S1766QuotSmallEquiv A.cover S1854TerminalCoherent.cover
    (S1854TerminalCover_isTerminal.from A.cover)

/-- It is the unique such morphism at the target hom universe. -/
theorem S1854TerminalMap01_unique (A : CoherentCover)
    (m : A ⟶ S1854TerminalCoherent) : m = S1854TerminalMap01 A := by
  apply (S1766QuotSmallEquiv A.cover S1854TerminalCoherent.cover).symm.injective
  have h : (S1766QuotSmallEquiv A.cover S1854TerminalCoherent.cover).symm
      (S1854TerminalMap01 A) = S1854TerminalCover_isTerminal.from A.cover :=
    Equiv.symm_apply_apply _ _
  rw [h]
  exact S1854TerminalCover_isTerminal.hom_ext _ _

/-- **The terminal coherent cover is terminal at the target hom universe too.** -/
noncomputable def S1854TerminalCoherent01_isTerminal :
    Limits.IsTerminal S1854TerminalCoherent :=
  Limits.IsTerminal.ofUniqueHom S1854TerminalMap01 S1854TerminalMap01_unique

/-- The coherent Category.{0,1} has a terminal object. -/
theorem S1854HasTerminal01 : Limits.HasTerminal CoherentCover :=
  S1854TerminalCoherent01_isTerminal.hasTerminal

end Coherent01Terminal

/-! ## 10. The transported structure, summarized -/

/-! **What is transported to the coherent covers, unconditionally.**

* the S1728 2-isomorphism cover category: fully and faithfully;
* S1809's actual Category.{0,1} at the target universe: fully and faithfully;
* S1828's slice model category: fully and faithfully, and R1 on it from the same two
  hypotheses S1828 uses;
* the terminal object (S1762's terminal cover is coherent), at both hom universes
  (S1854TerminalCoherent_isTerminal, S1854TerminalCoherent01_isTerminal).

The pullback and finite-coproduct structures are not transported here; their exact
remaining input is recorded as S1854PullbackFirstMissing and
S1854CoproductFirstMissing. -/

section Summary11

attribute [local instance] S1854CoherentCategory11

/-- The S1728-side transports, summarized. -/
theorem S1854TransportedSummary11 :
    S1854Forget11.Full ∧ S1854Forget11.Faithful ∧
      Limits.HasTerminal CoherentCover :=
  ⟨inferInstance, inferInstance, S1854HasTerminal⟩

end Summary11

section Summary01

attribute [local instance] S1854CoherentCategory01 S1809CoverCategory01

/-- The target-universe transports, summarized. -/
theorem S1854TransportedSummary01 :
    S1854Forget01.Full ∧ S1854Forget01.Faithful :=
  ⟨inferInstance, inferInstance⟩

end Summary01

/-! ## 11. Checks and axiom audit -/

#check S1854Vcomp
#check S1854ModelMap
#check S1854Compatible
#check S1854Compatible_of_rel
#check S1854Compatible_of_map
#check S1854CoherentMap
#check S1854CoherentQuot
#check S1854QuotToCover
#check S1854QuotToCover_surjective
#check S1854QuotToCover_injective
#check S1854QuotEquiv
#check S1854CategoryOfHomEquivOn
#check S1854CoherentCategory11
#check S1854CoherentCategory11_hom
#check @S1854Forget11
#check S1854Forget11_full_statement
#check S1854Forget11_faithful_statement
#check S1854Forget11_map_bijective
#check S1854StrongOfS1762
#check S1854TerminalStrong
#check S1854TerminalCoherent
#check S1854TerminalCover_eq
#check S1854TerminalCover_isTerminal
#check S1854TerminalMap
#check S1854TerminalCoherent_isTerminal
#check S1854HasTerminal
#check S1854TerminalModel_eq
#check S1854TerminalEnd
#check @S1854CoherentStrictHomEquiv
#check @S1854CoherentR1
#check S1854ModelSliceCategory
#check @S1854ModelSliceForget
#check S1854ModelSliceForget_full
#check S1854ModelSliceForget_faithful
#check S1854ModelSliceForget_map_bijective
#check S1854SliceHomEquiv
#check S1854CoherentR1_modelSlice
#check S1854PullbackApexCoherent
#check S1854CoproductApexCoherent
#check S1854PullbackTransport
#check S1854CoproductTransport
#check S1854PullbackFirstMissing
#check S1854CoproductFirstMissing
#check S1854LimitsFirstMissing
#check S1854SmallHom
#check S1854SmallHomEquiv
#check S1854CoherentCategory01
#check S1854CoherentCategory01_hom
#check @S1854Forget01
#check S1854Forget01_full_statement
#check S1854Forget01_faithful_statement
#check S1854Forget01_map_bijective
#check S1854TerminalMap01
#check S1854TerminalMap01_unique
#check S1854TerminalCoherent01_isTerminal
#check S1854HasTerminal01
#check S1854TransportedSummary11
#check S1854TransportedSummary01

#print axioms S1854Compatible_of_map
#print axioms S1854QuotToCover_surjective
#print axioms S1854QuotToCover_injective
#print axioms S1854CategoryOfHomEquivOn
#print axioms S1854CoherentCategory11
#print axioms S1854Forget11
#print axioms S1854Forget11_full
#print axioms S1854Forget11_faithful
#print axioms S1854StrongOfS1762
#print axioms S1854TerminalCoherent
#print axioms S1854TerminalCover_isTerminal
#print axioms S1854TerminalCoherent_isTerminal
#print axioms S1854HasTerminal
#print axioms S1854TerminalCoherent01_isTerminal
#print axioms S1854HasTerminal01
#print axioms S1854ModelSliceCategory
#print axioms S1854ModelSliceForget
#print axioms S1854ModelSliceForget_full
#print axioms S1854ModelSliceForget_faithful
#print axioms S1854CoherentR1_modelSlice
#print axioms S1854CoherentCategory01
#print axioms S1854Forget01
#print axioms S1854Forget01_full
#print axioms S1854Forget01_faithful

end LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
