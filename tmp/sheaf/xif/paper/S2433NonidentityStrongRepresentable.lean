/-
# S2433: a NON-identity StrongCover/CoherentCover example with
S2403RepresentableCoverMap data

## The question

S2403 records the exact representability data of a cover map

  g : S1728CoverMap A B

as a structure S2403RepresentableCoverMap g: both source fibres are
representable (source_fiber_eq, target_fiber_eq), the map g.map is
2-isomorphic to the representable strong transformation
S1742StrongTransOfHom g0 of an actual scheme morphism g0, and g0 is mono.
The only inhabitants produced in S2403 and S2409 were the *identity* cover maps
of the S2291 path cover and of the S1852 terminal (coherent) cover, both with
g0 = 1.  This file produces a genuinely non-identity example.

## What is built here (all unconditional)

1. S2433FoldCover : S1816Target, the finite etale cover of Spec R' whose
   carrier is the coproduct the coproduct of two copies of Spec R' and whose structure morphism is
   the fold S1850Fold.  Both finiteness and etaleness are S1850's actual
   theorems S1850Fold_finite, S1850Fold_etale; the cover is *not* the
   identity cover.

2. S2433FoldStrong : StrongCover S1726Orbicurve and
   S2433FoldCoherent : CoherentCover: the strong finite-etale structure is
   S1943's S1943Strong, the strong base-change structure of the extension map
   S1897ExtMap C (built from S1911's representable pullback theorem and the
   2-Yoneda transport of S1943).  Its source is the representable stack of the
   coproduct, so the cover has a genuinely non-identity structure map
   S1742StrongTransOfHom (S1850Fold).  Coherence is S1852's
   CoherentCover.ofStrong, whose unit is derived, not assumed.

3. The cover map S2433Map from the coherent *terminal* cover
   CoherentCover.cover S1852TerminalCoherent (source X.stack, map 1) to
   CoherentCover.cover S2433FoldCoherent, represented by the first coproduct
   inclusion S2433G0 : Spec R' -> the coproduct of two copies of Spec R':

     S2433Map.map = S1742StrongTransOfHom S2433G0.

   Its commuting 2-cell is the actual comparison
   vcomp (y(inl)) (y(fold)) = y(inl ; fold) = y(1) = 1, built from the
   representable composition equation S2398HomOfStrongTrans_vcomp, the
   splitting S1850Inl_fold and the 2-Yoneda comparison S1742.

4. S2433Representable : S2403RepresentableCoverMap S2433Map with

     sourceScheme = Spec R',  targetScheme = the coproduct of two copies of Spec R'
     (the scheme S1897CoverScheme S2433FoldCover), both fiber equalities
     definitional, g0 = S2433G0 (the first coproduct inclusion), and
     Mono S2433G0 from the *actual retraction* S1897CoverOver C:
     S2433G0_comp : S2433G0 ; S1897CoverOver C = 1.

5. **Non-identity certificates** (this is the point of the file):
   * S2433G0_comp exhibits S2433G0 as a split mono;
   * S2433FoldInl_ne_id, S2433Retraction_not_section: the other composite
     fold ; inl is *not* the identity (the second coproduct summand is moved
     onto the first, exactly S1850's argument);
   * S2433G0_not_iso : not IsIso S2433G0: the scheme morphism representing the
     cover map is not an isomorphism, so it cannot be an identity morphism
     transported along any object equality.  Hence the cover map is a genuine
     non-identity cover map between two coherent covers.

6. S2433TerminalSelfMapForcedIdentity: at a cover whose structure map is the
   identity, every represented *self* cover map is represented by the identity.
   This is why S2403/S2409 could only produce identity examples, and why the
   example here necessarily goes between two *different* coherent covers (the
   terminal one and the fold one).

7. **Use of the S2240/S2357 strong-cover data.**  For the fold coherent cover:
   * S2433FoldConeEssSurjAt: S2240ConeEssSurjAt B (cover S2433FoldCoherent)
     for every source cover B (the per-cover coherence of S2240);
   * S2433FoldPerCoverCoherence: S2357's
     S2357PerCoverCoherenceRequired B (cover S2433FoldCoherent);
   * S2433FoldPresentation and S2433FoldPresentation_finiteEtale: the S2130
     base-change presentation of the cover map S2433Map at the fold cover with
     finite etale projection (S2357StrongCoverPresentation).

## Honest boundary

* No existing definition is changed; the target S2403RepresentableCoverMap is
  used verbatim.
* No sorry, no axiom, no S2130ConcreteTwoPullback, no S2185StrictConeIso,
  no S2269 statement is asserted.  Only per-cover theorems of S2240/S2357 are
  used, and they are consequences of the strong cover datum.
* The two covers used are the coherent terminal cover and the coherent fold
  cover; the cover map is the coproduct inclusion, which is a monomorphism but
  not an isomorphism.  So this is a non-identity example in the strong sense
  of S2433G0_not_iso, not merely a map between distinct objects.
* The axiom footprint is propext, Classical.choice, Quot.sound only; see
  the audit block at the end.
-/

import tmp.sheaf.xif.paper.S1943AssembleEssSurjActual
import tmp.sheaf.xif.paper.S1850RefuteS1756Actual
import tmp.sheaf.xif.paper.S1844PointSeparatedActual
import tmp.sheaf.xif.paper.S2398HomOfStrongTransCompActual
import tmp.sheaf.xif.paper.S2403RepresentableExamplesActual
import tmp.sheaf.xif.paper.S2357CorrectedD6ApexActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open CategoryTheory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1943AssembleEssSurjActual
open LeanFormal.IUT.XiFPaper.S2398HomOfStrongTransCompActual
open LeanFormal.IUT.XiFPaper.S2403RepresentableExamplesActual
open LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual
open LeanFormal.IUT.XiFPaper.S2240StrictConeIsoActual
open LeanFormal.IUT.XiFPaper.S2357CorrectedD6ApexActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.XiFPaper.S2433NonidentityStrongRepresentable

/-! ## 1. The doubled affine base as a finite etale cover of Spec R' -/

/-- The affine base Spec R' as a scheme over Spec F'. -/
abbrev S2433T : SchemeOverField S1726K := S1726AffineOver

/-- The finite etale cover of Spec R' whose carrier is the coproduct of two copies of Spec R'
and whose structure morphism is the fold S1850Fold.  This is the
S1726AffineOver-derived cover used for the non-identity example. -/
noncomputable def S2433FoldCover : S1816Target :=
  FiniteEtaleCover.mk (S := S1816Base) (X := (S1850P S2433T).left)
    (S1850Fold S2433T).left (S1850Fold_etale S2433T) (S1850Fold_finite S2433T)

/-- The source scheme of the fold cover, as a scheme over Spec F', is the
doubled affine base. -/
@[simp] theorem S2433FoldCover_scheme_left :
    (S1897CoverScheme S2433FoldCover).left = (S1850P S2433T).left := rfl

/-! ## 2. The first coproduct inclusion and its retraction -/

/-- The first coproduct inclusion Spec R' -> the coproduct of two copies of Spec R' as a morphism of
schemes over Spec F' into the fold cover. -/
noncomputable def S2433G0 : S2433T ⟶ S1897CoverScheme S2433FoldCover :=
  Over.homMk (Limits.coprod.inl : S2433T.left ⟶ (S1850P S2433T).left) (by
    show Limits.coprod.inl ≫ ((S1850Fold S2433T).left ≫ S2433T.hom) = S2433T.hom
    rw [← Category.assoc, S1850Fold_left, Limits.coprod.inl_desc, Category.id_comp])

/-- The underlying scheme morphism of S2433G0 is the coproduct inclusion. -/
@[simp] theorem S2433G0_left : Over.Hom.left S2433G0 = Limits.coprod.inl := rfl

/-- **S2433G0 is a split monomorphism**: the structure morphism of the fold
cover retracts it. -/
theorem S2433G0_comp :
    S2433G0 ≫ S1897CoverOver S2433FoldCover = 𝟙 S2433T := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S2433G0 ≫ S1897CoverOver S2433FoldCover) = Over.Hom.left (𝟙 S2433T)
  rw [Over.comp_left, Over.id_left, S1897CoverOver_left]
  show Limits.coprod.inl ≫ (S1850Fold S2433T).left = 𝟙 S2433T.left
  rw [S1850Fold_left, Limits.coprod.inl_desc]

/-- The representing scheme morphism is monic. -/
theorem S2433G0_mono : Mono S2433G0 := by
  haveI : IsSplitMono S2433G0 :=
    ⟨⟨{ retraction := S1897CoverOver S2433FoldCover, id := S2433G0_comp }⟩⟩
  exact inferInstance

/-! ## 3. The strong and coherent fold cover -/

/-- **The fold cover is a strong cover**: its structure map is S1943's strong
finite-etale extension map, i.e. the map represented by the fold. -/
noncomputable def S2433FoldStrong : StrongCover S1726Orbicurve where
  source := S1897ExtSource S2433FoldCover
  map := S1897ExtMap S2433FoldCover
  finiteEtale := S1943Strong S2433FoldCover

/-- **The fold cover is coherent** (its unit is derived from the full
2-universal property, not assumed). -/
noncomputable def S2433FoldCoherent : CoherentCover :=
  CoherentCover.ofStrong S2433FoldStrong

/-- Its underlying recorded cover has the representable source of the coproduct. -/
@[simp] theorem S2433FoldCoherent_source_fiber :
    (CoherentCover.cover S2433FoldCoherent).source.fiber
      = S1742YS (F := S1726K) (S1897CoverScheme S2433FoldCover) := rfl

/-- The terminal coherent cover has the representable source Spec R'. -/
@[simp] theorem S2433Terminal_source_fiber :
    (CoherentCover.cover S1852TerminalCoherent).source.fiber
      = S1742YS (F := S1726K) S2433T := rfl

/-! ## 4. The 2-cell toolkit -/

/-- The identity strong transformation has underlying scheme morphism the
identity. -/
theorem S2433HomOfId :
    S1742HomOfStrongTrans (F := S1726K)
      (Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S2433T)) = 𝟙 S2433T := by
  unfold S1742HomOfStrongTrans
  rfl

/-- The identity affine map is 2-isomorphic to the identity strong
transformation. -/
noncomputable def S2433IdIso :
    Iso (S1742StrongTransOfHom (F := S1726K) (𝟙 S2433T))
      (Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S2433T)) := by
  have e := S1742StrongTransIsoOfHom (F := S1726K) (S := S2433T) (T := S2433T)
    (eta := Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S2433T))
  rw [S2433HomOfId] at e
  exact e

/-- The representable strong transformation of a composite scheme map is
2-isomorphic to the vertical composite of the representable strong
transformations.  This is S2398's composition equation in iso form. -/
noncomputable def S2433StrongTransOfHomCompIso
    {X1 X2 X3 : SchemeOverField S1726K} (a : X1 ⟶ X2) (b : X2 ⟶ X3) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) a)
        (S1742StrongTransOfHom (F := S1726K) b))
      (S1742StrongTransOfHom (F := S1726K) (a ≫ b)) := by
  have h := S1742StrongTransIsoOfHom (F := S1726K) (S := X1) (T := X3)
    (eta := Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1726K) a)
      (S1742StrongTransOfHom (F := S1726K) b))
  rw [S2398HomOfStrongTrans_vcomp (F := S1726K) a b] at h
  exact h.symm

/-! ## 5. The non-identity cover map between the two coherent covers -/

/-- **The non-identity cover map**: from the coherent terminal cover (source
X.stack, structure map 1) to the coherent fold cover (source the
representable stack of the coproduct of two copies of Spec R', structure map the fold).  Its
underlying strong transformation is the representable map of the first
coproduct inclusion. -/
noncomputable def S2433Map :
    S1728CoverMap (CoherentCover.cover S1852TerminalCoherent)
      (CoherentCover.cover S2433FoldCoherent) where
  map := S1742StrongTransOfHom (F := S1726K) S2433G0
  commutes := by
    change Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) S2433G0)
        (S1742StrongTransOfHom (F := S1726K) (S1897CoverOver S2433FoldCover)))
      (Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S2433T))
    exact (S2433StrongTransOfHomCompIso S2433G0
      (S1897CoverOver S2433FoldCover)).trans
      ((eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K)) S2433G0_comp)).trans
        S2433IdIso)

/-- **The S2403 representability data of S2433Map**: both source fibres are
representable, the map is 2-isomorphic to the representable map of the first
coproduct inclusion, and that scheme morphism is monic. -/
noncomputable def S2433Representable :
    S2403RepresentableCoverMap S2433Map where
  sourceScheme := S2433T
  targetScheme := S1897CoverScheme S2433FoldCover
  source_fiber_eq := rfl
  target_fiber_eq := rfl
  g0 := S2433G0
  map_iso := by
    refine ⟨?_⟩
    change Iso (S1742StrongTransOfHom (F := S1726K) S2433G0)
      (S1742StrongTransOfHom (F := S1726K) S2433G0)
    exact Iso.refl _
  mono := S2433G0_mono

/-! ## 6. Non-identity certificates -/

/-- The fold composed with the first inclusion is not the identity of the
doubled affine base: the second summand is moved onto the first.  This is
S1850's computation, at the level of the underlying schemes. -/
theorem S2433FoldInl_ne_id :
    (S1850Fold S2433T).left ≫
        (Limits.coprod.inl : S2433T.left ⟶ (S1850P S2433T).left) ≠
      𝟙 (S1850P S2433T).left := by
  intro h
  haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
  have hne : Nonempty (Spec (CommRingCat.of S1726CoordinateRing)) := inferInstance
  let x : S2433T.left := Classical.choice hne
  let y : (S1850P S2433T).left :=
    (Limits.coprod.inr : S2433T.left ⟶ (S1850P S2433T).left) x
  have hx := congrArg
    (fun f : (S1850P S2433T).left ⟶ (S1850P S2433T).left => f y) h
  change (Limits.coprod.desc (𝟙 S2433T.left) (𝟙 S2433T.left) ≫
      Limits.coprod.inl) y = (𝟙 ((S1850P S2433T).left)) y at hx
  rw [Scheme.Hom.comp_apply] at hx
  rw [show (Limits.coprod.desc (𝟙 S2433T.left) (𝟙 S2433T.left)) y =
      (Limits.coprod.inr ≫
        Limits.coprod.desc (𝟙 S2433T.left) (𝟙 S2433T.left)) x from rfl,
    Limits.coprod.inr_desc] at hx
  have hxid : ((𝟙 S2433T.left : S2433T.left ⟶ S2433T.left) x) = x := rfl
  have hy : y = (Limits.coprod.inr : S2433T.left ⟶ (S1850P S2433T).left) x := rfl
  rw [hxid, hy] at hx
  exact (AlgebraicGeometry.inl_ne_inr (X := S2433T.left) (Y := S2433T.left) x x) hx

/-- The retraction is not a two-sided inverse: the other composite is not the
identity of the fold cover. -/
theorem S2433Retraction_not_section :
    S1897CoverOver S2433FoldCover ≫ S2433G0 ≠
      𝟙 (S1897CoverScheme S2433FoldCover) := by
  intro h
  have hleft := congrArg Over.Hom.left h
  rw [Over.comp_left, Over.id_left, S1897CoverOver_left, S2433G0_left] at hleft
  exact S2433FoldInl_ne_id hleft

/-- **The representing scheme morphism is not an isomorphism**, hence is not an
identity morphism transported along any equality of objects. -/
theorem S2433G0_not_iso : ¬ IsIso S2433G0 := by
  intro hiso
  have hsec : S1897CoverOver S2433FoldCover ≫ S2433G0 =
      𝟙 (S1897CoverScheme S2433FoldCover) := by
    have h1 : S1897CoverOver S2433FoldCover = inv S2433G0 :=
      IsIso.eq_inv_of_hom_inv_id S2433G0_comp
    rw [h1, IsIso.inv_hom_id]
  exact S2433Retraction_not_section hsec

/-! ## 7. Why the previous examples had to be identities -/

/-- **Self cover maps of the terminal coherent cover are represented by the
identity.**  Its structure map is the identity, and then the commuting 2-cell of
any represented self cover map forces the representing scheme map to be the
identity, so no non-identity example can live at the terminal cover alone.
This is the structural reason for going from the terminal cover to the fold
cover. -/
theorem S2433TerminalSelfMapForcedIdentity
    (g : S1728CoverMap (CoherentCover.cover S1852TerminalCoherent)
      (CoherentCover.cover S1852TerminalCoherent))
    (g0 : S2433T ⟶ S2433T)
    (hg : g.map = S1742StrongTransOfHom (F := S1726K) g0) :
    g0 = 𝟙 S2433T := by
  have hcomm : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom (F := S1726K) g0)
        (Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S2433T)))
      (Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S2433T)) := by
    rw [← hg]
    exact g.commutes
  have h1 : Iso (S1742StrongTransOfHom (F := S1726K) g0)
      (Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S2433T)) :=
    (Pseudofunctor.StrongTrans.rightUnitor
      (S1742StrongTransOfHom (F := S1726K) g0)).symm.trans hcomm
  have hEq : S1742HomOfStrongTrans
        (S1742StrongTransOfHom (F := S1726K) g0) =
      S1742HomOfStrongTrans
        (Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S2433T)) :=
    S1742HomOfStrongTrans_congr h1
  rw [S1742HomOfStrongTrans_strongTransOfHom, S2433HomOfId] at hEq
  exact hEq

/-! ## 8. Consumers: the S2240 / S2357 strong-cover data at the fold cover -/

/-- The fold coherent cover satisfies S2240's per-cover coherence for every
source cover. -/
theorem S2433FoldConeEssSurjAt (B : S1728Cover) :
    S2240ConeEssSurjAt B (CoherentCover.cover S2433FoldCoherent) :=
  S2240ConeEssSurjAt_of_strongCover S2433FoldStrong B

/-- The fold coherent cover satisfies S2357's per-cover coherence statement. -/
theorem S2433FoldPerCoverCoherence (B : S1728Cover) :
    S2357PerCoverCoherenceRequired B (CoherentCover.cover S2433FoldCoherent) :=
  S2357StrongCoverCoherence S2433FoldStrong B

/-- The S2130 base-change presentation of the non-identity cover map at the fold
cover. -/
noncomputable def S2433FoldPresentation (T' : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T')
      (CoherentCover.cover S1852TerminalCoherent).source.fiber) :
    EtaleStackBaseChangePresentation S2433Map.map T'
      (S2130PtC S2433Map T' ptA) :=
  S2357StrongCoverPresentation S2433FoldStrong
    (CoherentCover.cover S1852TerminalCoherent)
    (CoherentCover.cover S1852TerminalCoherent) S2433Map S2433Map T' ptA

/-- Its projection is finite and etale. -/
theorem S2433FoldPresentation_finiteEtale (T' : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T')
      (CoherentCover.cover S1852TerminalCoherent).source.fiber) :
    IsFinite ((S2433FoldPresentation T' ptA).projection.left) ∧
      Etale ((S2433FoldPresentation T' ptA).projection.left) :=
  S2357StrongCoverPresentation_finiteEtale S2433FoldStrong
    (CoherentCover.cover S1852TerminalCoherent)
    (CoherentCover.cover S1852TerminalCoherent) S2433Map S2433Map T' ptA

/-! ## 9. Checks and axiom footprint -/

#check S2433FoldCover
#check S2433G0
#check S2433G0_comp
#check S2433G0_mono
#check S2433FoldStrong
#check S2433FoldCoherent
#check S2433Map
#check S2433Representable
#check S2433FoldInl_ne_id
#check S2433Retraction_not_section
#check S2433G0_not_iso
#check S2433TerminalSelfMapForcedIdentity
#check S2433FoldConeEssSurjAt
#check S2433FoldPerCoverCoherence
#check S2433FoldPresentation
#check S2433FoldPresentation_finiteEtale

#print axioms S2433FoldCover
#print axioms S2433G0
#print axioms S2433G0_comp
#print axioms S2433G0_mono
#print axioms S2433FoldStrong
#print axioms S2433FoldCoherent
#print axioms S2433Map
#print axioms S2433Representable
#print axioms S2433FoldInl_ne_id
#print axioms S2433Retraction_not_section
#print axioms S2433G0_not_iso
#print axioms S2433TerminalSelfMapForcedIdentity
#print axioms S2433FoldConeEssSurjAt
#print axioms S2433FoldPerCoverCoherence
#print axioms S2433FoldPresentation
#print axioms S2433FoldPresentation_finiteEtale

end LeanFormal.IUT.XiFPaper.S2433NonidentityStrongRepresentable
end
