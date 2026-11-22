/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1744Category01AssemblyActual

/-!
# S1766: is the canonical identity-point affine model action injective? (R2a)

S1744 constructed, for the actual S1726 D6 orbicurve and the affine
identity-point model S1733Model A, the action

  S1744ModelMapOfCoverMap A B : S1728CoverMap A B -> (S1733Model A --> S1733Model B)

of actual finite-etale cover maps on the canonical models, and isolated the
comparison S1744CanonicalModelHomBijective into injectivity **R2a** and
surjectivity **R2b**.  S1744 suspected that R2a might fail because the
construction "only sees the identity point", so two cover maps that differ
away from that point could a priori have the same model morphism.

This file settles R2a.  The answer is sharper than either the positive or the
negative reading of S1744, and it is proved, not assumed.

## 1. The kernel of the action is exactly 2-isomorphism (unconditional)

Writing

  S1766Phi A B f = ((toSource A) o f.map) o lift B

for the strong transformation whose 2-Yoneda evaluation is the action
(S1766_act_def), we prove

  S1766_act_eq_iff_coverMapRel:
    act f = act g  <->  S1728CoverMapRel f g,

i.e. two cover maps have the same canonical model morphism **iff their
underlying strong transformations are 2-isomorphic**.  Both inclusions are
unconditional:

* (<=) whisker the 2-isomorphism by toSource A and lift B, then apply
  2-Yoneda (S1742HomOfStrongTrans_congr);
* (=>) use 2-Yoneda to get Phi f = Phi g (up to 2-isomorphism), cancel lift B
  on the right by S1743's section lift B o toSource B = id
  (S1743ModelSection), and cancel toSource A on the left by
  lift A o toSource A = id (S1766_map_iso_of_phi_iso).

No hypothesis on the missing retraction half of stack representability is
needed: the two *sections* already supplied by S1743 suffice.  In particular
the action is precisely the 2-isomorphism quotient of cover maps, and is
always injective on 2-isomorphism classes:

  S1766QuotAct and S1766QuotAct_injective.

This also explains why "more test points" cannot repair raw injectivity: any
functorial action on strong transformations is automatically constant on
2-isomorphism classes, and the identity point alone already realises the
whole 2-isomorphism quotient.  The identity point of S1733 is the identity
1-cell of the base stack, so the base change is the identity base change, not
a lossy closed-point fibre; S1743's section shows the model maps *onto* the
cover source (lift o toSource = id).

## 2. Exact status of R2a on raw cover maps

Consequently, for the canonical action

  S1766_raw_injective_iff_discrete:
    S1744CanonicalModelHomActionInjective S1744CanonicalModelHomActionActual
      <-> S1766CoverMapDiscrete,

where S1766CoverMapDiscrete says that every S1728CoverMapRel-class is a
singleton.  Equivalently (S1766_coverMapDiscrete_iff), every 2-isomorphism
between the underlying strong transformations of two cover maps must be an
equality of those transformations.  The second field commutes of a cover map
is a subsingleton (S1766_commutes_subsingleton; the target stack is
representable), so this discreteness is exactly the only remaining content.

Thus R2a on raw maps is **not** a statement about the canonical model losing
geometric information: it is exactly the discreteness of the raw cover-map
hom types with respect to 2-isomorphism.  An actual counterexample must be a
pair f != g of cover maps with f.map = g.map (2-isomorphic)
(S1766_counterexample, S1766_not_injective_iff_actualCounterexample); such a
pair cannot be excluded by extra model data of functorial origin.

In the present tree no cover object is constructed, so no unconditional pair
can be exhibited.  For representable cover sources (the situation of a genuine
2-pullback: the identity point is the whole base) there are no nontrivial
2-cells, hence R2a holds.  The formal obstruction is that
EtaleStackBaseChangePresentation.isPullback is only a weak two-pullback
witness (no one-cell uniqueness and no inverse 2-cell); it does not force the
comparison toSource to be an equivalence.  Adding that missing
one-cell/equivalence datum would give discreteness of representable sources
and hence R2a; it is *not* needed for the kernel computation above.

## 3. Correct small model choice and exact missing data

* Small hom model: use the 2-isomorphism quotient, realised as the image of
  the canonical action inside the Type-0 model hom types,

    S1766QuotSmallCarrier A B = Set.range (S1766QuotAct A B).

  It is Type 0 and equivalent to the genuine cover-map quotient
  (S1766QuotSmallEquiv).  This is the model the category/slice comparison
  needs (S1728ActualCategory11, S1733CoverSliceEquivalence).

* The raw-map target of S1733AffineCoverModel.homEquiv is the wrong shape
  unless one adds a discreteness certificate: S1766CoverMapDiscrete is
  exactly the extra datum, and with it the raw action is injective
  (S1766_raw_injective_of_discrete).

* Recording all test points/homs, or the finite-etale algebra model, helps
  only after one has a *strict* (one-cell unique) representation of the
  cover source.  For the split degree-two cover of the actual model
  (S1726FiniteEtaleAlgebra = F' x F', sheet swap) the deck transformation is
  a genuine algebra automorphism, hence a genuinely different model morphism,
  not a 2-cell collision.

* R2b (surjectivity/descent) is untouched here and remains the separate
  geometric gap.

No sorry, no new axiom, no Shrink/PUnit, and no ULift coercion of the
mathematical data (the only ULift occurrence is the proof-level
`ULift.ext` for morphisms in Mathlib's `Discrete` category).  The target
OrbicurveEtaleFundamentalGroup is not constructed.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1766CanonicalModelInjectivityActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1744Category01AssemblyActual

/-! ## 1. The action and the strong transformation computing it -/

/-- The representable etale pseudofunctor of a scheme over the S1726 field. -/
noncomputable abbrev S1766Y (S : Iut.SchemeOverField S1726K) :
    Iut.EtaleStackPseudofunctor S1726K :=
  Iut.schemeRepresentableEtalePseudofunctor S1726K S

/-- The strong transformation whose 2-Yoneda evaluation is the canonical
action. -/
noncomputable def S1766Phi (A B : S1728Cover) (f : S1728CoverMap A B) :
    Pseudofunctor.StrongTrans (S1766Y (S1733Model A)) (S1766Y (S1733Model B)) :=
  Pseudofunctor.StrongTrans.vcomp
    (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
    (S1743Lift B)

/-- The defining computation rule of the action. -/
theorem S1766_act_def (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1744ModelMapOfCoverMap A B f = S1742HomOfStrongTrans (S1766Phi A B f) := rfl

/-- 2-Yoneda: equal evaluations give 2-isomorphic strong transformations. -/
theorem S1766_isoOfHomEq {S T : Iut.SchemeOverField S1726K}
    {eta theta : Pseudofunctor.StrongTrans (S1766Y S) (S1766Y T)}
    (h : S1742HomOfStrongTrans eta = S1742HomOfStrongTrans theta) :
    Nonempty (eta ≅ theta) := by
  have h' : S1742StrongTransOfHom (F := S1726K) (S1742HomOfStrongTrans eta) =
      S1742StrongTransOfHom (F := S1726K) (S1742HomOfStrongTrans theta) := by
    rw [h]
  exact ⟨(S1742StrongTransIsoOfHom eta).symm ≪≫ eqToIso h' ≪≫
    S1742StrongTransIsoOfHom theta⟩

/-- Equality of the canonical action is exactly 2-isomorphism of S1766Phi. -/
theorem S1766_modelMap_eq_iff_phi_iso (A B : S1728Cover)
    (f g : S1728CoverMap A B) :
    S1744ModelMapOfCoverMap A B f = S1744ModelMapOfCoverMap A B g ↔
      Nonempty (S1766Phi A B f ≅ S1766Phi A B g) := by
  constructor
  · intro h
    apply S1766_isoOfHomEq
    have h' : S1742HomOfStrongTrans (F := S1726K) (S := S1733Model A)
        (T := S1733Model B) (S1766Phi A B f) =
        S1742HomOfStrongTrans (F := S1726K) (S := S1733Model A)
          (T := S1733Model B) (S1766Phi A B g) := h
    simpa only [S1766_act_def] using h'
  · rintro ⟨e⟩
    simpa only [S1766_act_def] using
      (S1742HomOfStrongTrans_congr (F := S1726K) e)

/-! ## 2. The section supplied by S1743 and the two cancellations -/

/-- Sharp form of the first half of stack representability: the S1743 lift is
a section of the base-change comparison. -/
theorem S1766_lift_toSource (B : S1728Cover) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1744BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.id B.source.fiber)) :=
  ⟨(S1744BaseChange B).isPullback.liftToX B.source.fiber (S1743IdentityCone B)⟩

/-- Right cancellation: composing with the comparison to the base and using the
lift recovers the intermediate map. -/
theorem S1766_phi_comp_toSource_iso (A B : S1728Cover)
    (X : Pseudofunctor.StrongTrans (S1766Y (S1733Model A)) B.source.fiber) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp X (S1743Lift B))
        (S1744BaseChange B).toSource)
      X) := by
  obtain ⟨e⟩ := S1766_lift_toSource B
  have h1 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp X (S1743Lift B))
        (S1744BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.vcomp X
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1744BaseChange B).toSource)) :=
    @Bicategory.associator (Iut.EtaleStackPseudofunctor S1726K) _
      (S1766Y (S1733Model A)) B.source.fiber (S1766Y (S1733Model B)) B.source.fiber
      X (S1743Lift B) (S1744BaseChange B).toSource
  have h2 : Iso
      (Pseudofunctor.StrongTrans.vcomp X
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1744BaseChange B).toSource))
      (Pseudofunctor.StrongTrans.vcomp X
        (Pseudofunctor.StrongTrans.id B.source.fiber)) :=
    @Bicategory.whiskerLeftIso (Iut.EtaleStackPseudofunctor S1726K) _
      (S1766Y (S1733Model A)) B.source.fiber B.source.fiber
      X
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1744BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.id B.source.fiber)
      e
  have h3 : Iso
      (Pseudofunctor.StrongTrans.vcomp X (Pseudofunctor.StrongTrans.id B.source.fiber)) X :=
    Pseudofunctor.StrongTrans.rightUnitor X
  exact ⟨h1.trans (h2.trans h3)⟩

/-- A 2-isomorphism of cover maps induces a 2-isomorphism of S1766Phi. -/
theorem S1766_phi_iso_of_map_iso (A B : S1728Cover) {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) :
    Nonempty (S1766Phi A B f ≅ S1766Phi A B g) := by
  have h1 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map) :=
    @Bicategory.whiskerLeftIso (Iut.EtaleStackPseudofunctor S1726K) _
      (S1766Y (S1733Model A)) A.source.fiber B.source.fiber
      (S1744BaseChange A).toSource f.map g.map e
  exact ⟨@Bicategory.whiskerRightIso (Iut.EtaleStackPseudofunctor S1726K) _
    (S1766Y (S1733Model A)) B.source.fiber (S1766Y (S1733Model B))
    (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
    (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map)
    h1 (S1743Lift B)⟩

/-- **Cancellation.**  If the two composites attached to two cover maps are
2-isomorphic, then the underlying strong transformations are 2-isomorphic.
No hypothesis beyond S1743's section is used. -/
theorem S1766_map_iso_of_phi_iso (A B : S1728Cover) {f g : S1728CoverMap A B}
    (h : Nonempty (S1766Phi A B f ≅ S1766Phi A B g)) :
    Nonempty (f.map ≅ g.map) := by
  obtain ⟨e⟩ := h
  have eR : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1766Phi A B f) (S1744BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.vcomp (S1766Phi A B g) (S1744BaseChange B).toSource) :=
    @Bicategory.whiskerRightIso (Iut.EtaleStackPseudofunctor S1726K) _
      (S1766Y (S1733Model A)) (S1766Y (S1733Model B)) B.source.fiber
      (S1766Phi A B f) (S1766Phi A B g) e (S1744BaseChange B).toSource
  have hf1 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1766Phi A B f) (S1744BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1744BaseChange B).toSource)) :=
    @Bicategory.associator (Iut.EtaleStackPseudofunctor S1726K) _
      (S1766Y (S1733Model A)) B.source.fiber (S1766Y (S1733Model B)) B.source.fiber
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
      (S1743Lift B) (S1744BaseChange B).toSource
  have hf2 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1744BaseChange B).toSource))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
        (Pseudofunctor.StrongTrans.id B.source.fiber)) :=
    @Bicategory.whiskerLeftIso (Iut.EtaleStackPseudofunctor S1726K) _
      (S1766Y (S1733Model A)) B.source.fiber B.source.fiber
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1744BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.id B.source.fiber) (S1766_lift_toSource B).some
  have hf3 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
        (Pseudofunctor.StrongTrans.id B.source.fiber))
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map) :=
    Pseudofunctor.StrongTrans.rightUnitor
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
  have hf : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1766Phi A B f) (S1744BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map) :=
    hf1.trans (hf2.trans hf3)
  have hg1 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1766Phi A B g) (S1744BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map)
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1744BaseChange B).toSource)) :=
    @Bicategory.associator (Iut.EtaleStackPseudofunctor S1726K) _
      (S1766Y (S1733Model A)) B.source.fiber (S1766Y (S1733Model B)) B.source.fiber
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map)
      (S1743Lift B) (S1744BaseChange B).toSource
  have hg2 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map)
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1744BaseChange B).toSource))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map)
        (Pseudofunctor.StrongTrans.id B.source.fiber)) :=
    @Bicategory.whiskerLeftIso (Iut.EtaleStackPseudofunctor S1726K) _
      (S1766Y (S1733Model A)) B.source.fiber B.source.fiber
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map)
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1744BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.id B.source.fiber) (S1766_lift_toSource B).some
  have hg3 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map)
        (Pseudofunctor.StrongTrans.id B.source.fiber))
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map) :=
    Pseudofunctor.StrongTrans.rightUnitor
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map)
  have hg : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1766Phi A B g) (S1744BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map) :=
    hg1.trans (hg2.trans hg3)
  have eMid : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map) :=
    hf.symm.trans (eR.trans hg)
  have eL : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map))
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map)) :=
    @Bicategory.whiskerLeftIso (Iut.EtaleStackPseudofunctor S1726K) _
      (A.source.fiber) (S1766Y (S1733Model A)) B.source.fiber
      (S1743Lift A)
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map) eMid
  have secA : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1744BaseChange A).toSource)
      (Pseudofunctor.StrongTrans.id A.source.fiber) := (S1766_lift_toSource A).some
  have outf1 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1744BaseChange A).toSource)
        f.map) :=
    (@Bicategory.associator (Iut.EtaleStackPseudofunctor S1726K) _
      (A.source.fiber) (S1766Y (S1733Model A)) (A.source.fiber) (B.source.fiber)
      (S1743Lift A) (S1744BaseChange A).toSource f.map).symm
  have outf2 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1744BaseChange A).toSource)
        f.map)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id A.source.fiber) f.map) :=
    @Bicategory.whiskerRightIso (Iut.EtaleStackPseudofunctor S1726K) _
      (A.source.fiber) (A.source.fiber) (B.source.fiber)
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1744BaseChange A).toSource)
      (Pseudofunctor.StrongTrans.id A.source.fiber) secA f.map
  have outf3 : Iso
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id A.source.fiber) f.map)
      f.map :=
    Pseudofunctor.StrongTrans.leftUnitor f.map
  have outf : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)) f.map :=
    outf1.trans (outf2.trans outf3)
  have outg1 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1744BaseChange A).toSource)
        g.map) :=
    (@Bicategory.associator (Iut.EtaleStackPseudofunctor S1726K) _
      (A.source.fiber) (S1766Y (S1733Model A)) (A.source.fiber) (B.source.fiber)
      (S1743Lift A) (S1744BaseChange A).toSource g.map).symm
  have outg2 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1744BaseChange A).toSource)
        g.map)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id A.source.fiber) g.map) :=
    @Bicategory.whiskerRightIso (Iut.EtaleStackPseudofunctor S1726K) _
      (A.source.fiber) (A.source.fiber) (B.source.fiber)
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1744BaseChange A).toSource)
      (Pseudofunctor.StrongTrans.id A.source.fiber) secA g.map
  have outg3 : Iso
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id A.source.fiber) g.map)
      g.map :=
    Pseudofunctor.StrongTrans.leftUnitor g.map
  have outg : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource g.map)) g.map :=
    outg1.trans (outg2.trans outg3)
  exact ⟨outf.symm.trans (eL.trans outg)⟩

/-! ## 3. The kernel theorem -/

/-- **The kernel of the canonical action is exactly 2-isomorphism.** -/
theorem S1766_act_eq_iff_coverMapRel (A B : S1728Cover)
    (f g : S1728CoverMap A B) :
    S1744ModelMapOfCoverMap A B f = S1744ModelMapOfCoverMap A B g ↔
      S1728CoverMapRel f g := by
  change _ = _ ↔ Nonempty (f.map ≅ g.map)
  exact (S1766_modelMap_eq_iff_phi_iso A B f g).trans
    ⟨fun h => S1766_map_iso_of_phi_iso A B h,
     fun h => S1766_phi_iso_of_map_iso A B h.some⟩

/-- The same kernel statement for the canonical action itself. -/
theorem S1766CanonicalAct_eq_iff_coverMapRel (A B : S1728Cover)
    (f g : S1728CoverMap A B) :
    S1744CanonicalModelHomActionActual A B f =
        S1744CanonicalModelHomActionActual A B g ↔
      S1728CoverMapRel f g :=
  S1766_act_eq_iff_coverMapRel A B f g

/-! ## 4. The action on 2-isomorphism classes is injective -/

/-- The canonical action, descended to the 2-isomorphism quotient of cover
maps.  It is well defined by the kernel theorem. -/
noncomputable def S1766QuotAct (A B : S1728Cover) :
    Quot (fun f g : S1728CoverMap A B => S1728CoverMapRel f g) →
      (S1733Model A ⟶ S1733Model B) :=
  Quot.lift (fun f => S1744ModelMapOfCoverMap A B f)
    (fun f g h => (S1766_act_eq_iff_coverMapRel A B f g).mpr h)

/-- Computation rule of the descended action. -/
@[simp] theorem S1766QuotAct_mk (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1766QuotAct A B (Quot.mk _ f) = S1744ModelMapOfCoverMap A B f := rfl

/-- **The canonical action is injective on 2-isomorphism classes.** -/
theorem S1766QuotAct_injective (A B : S1728Cover) :
    Function.Injective (S1766QuotAct A B) := by
  intro q1 q2 h
  revert h
  refine Quot.inductionOn q1 ?_
  intro f
  refine Quot.inductionOn q2 ?_
  intro g h
  apply Quot.sound
  exact (S1766_act_eq_iff_coverMapRel A B f g).mp h

/-! ## 5. Raw injectivity is exactly discreteness of cover maps -/

/-- The exact residual of R2a on raw cover maps: every 2-isomorphism class of
cover maps is a singleton. -/
def S1766CoverMapDiscrete : Prop :=
  ∀ (A B : S1728Cover) (f g : S1728CoverMap A B),
    S1728CoverMapRel f g → f = g

/-- **R2a on raw maps is equivalent to discreteness of cover maps.** -/
theorem S1766_raw_injective_iff_discrete :
    S1744CanonicalModelHomActionInjective S1744CanonicalModelHomActionActual ↔
      S1766CoverMapDiscrete := by
  constructor
  · intro hinj A B f g h
    exact hinj A B ((S1766_act_eq_iff_coverMapRel A B f g).mpr h)
  · intro hdisc A B f g h
    exact hdisc A B f g ((S1766_act_eq_iff_coverMapRel A B f g).mp h)

/-- R2a holds once discreteness is supplied. -/
theorem S1766_raw_injective_of_discrete (h : S1766CoverMapDiscrete) :
    S1744CanonicalModelHomActionInjective S1744CanonicalModelHomActionActual :=
  S1766_raw_injective_iff_discrete.mpr h

/-- The exact missing statement for R2a, named for downstream use. -/
def S1766RawInjectivityExactMissing : Prop := S1766CoverMapDiscrete

/-- The named missing statement is exactly R2a. -/
theorem S1766RawInjectivityExactMissing_iff :
    S1766RawInjectivityExactMissing ↔
      S1744CanonicalModelHomActionInjective S1744CanonicalModelHomActionActual :=
  S1766_raw_injective_iff_discrete.symm

/-! ## 6. The exact shape of a raw counterexample -/

/-- An actual counterexample to R2a: two distinct cover maps whose underlying
strong transformations are 2-isomorphic (so they have the same canonical model
morphism). -/
def S1766ActualCounterexample : Prop :=
  ∃ (A B : S1728Cover) (f g : S1728CoverMap A B),
    f ≠ g ∧ S1728CoverMapRel f g

/-- Any pair of distinct 2-isomorphic cover maps gives the same model
morphism and refutes R2a. -/
theorem S1766_counterexample (A B : S1728Cover) (f g : S1728CoverMap A B)
    (hrel : S1728CoverMapRel f g) (hne : f ≠ g) :
    ¬ S1744CanonicalModelHomActionInjective S1744CanonicalModelHomActionActual := by
  intro hinj
  exact hne (hinj A B ((S1766_act_eq_iff_coverMapRel A B f g).mpr hrel))

/-- The explicit collision: two distinct cover maps with the same canonical
model morphism. -/
theorem S1766_collision (A B : S1728Cover) (f g : S1728CoverMap A B)
    (hrel : S1728CoverMapRel f g) :
    S1744CanonicalModelHomActionActual A B f =
        S1744CanonicalModelHomActionActual A B g ∧
      S1728CoverMapRel f g :=
  ⟨(S1766_act_eq_iff_coverMapRel A B f g).mpr hrel, hrel⟩

/-- R2a fails exactly when an actual counterexample exists. -/
theorem S1766_not_injective_iff_actualCounterexample :
    ¬ S1744CanonicalModelHomActionInjective S1744CanonicalModelHomActionActual ↔
      S1766ActualCounterexample := by
  rw [S1766_raw_injective_iff_discrete]
  constructor
  · intro h
    by_contra hce
    apply h
    intro A B f g hrel
    by_contra hne
    exact hce ⟨A, B, f, g, hne, hrel⟩
  · rintro ⟨A, B, f, g, hne, hrel⟩ hd
    exact hne (hd A B f g hrel)

/-- R2a holds exactly when no actual counterexample exists. -/
theorem S1766_injective_iff_no_actualCounterexample :
    S1744CanonicalModelHomActionInjective S1744CanonicalModelHomActionActual ↔
      ¬ S1766ActualCounterexample := by
  rw [S1766_raw_injective_iff_discrete]
  constructor
  · rintro hd ⟨A, B, f, g, hne, hrel⟩
    exact hne (hd A B f g hrel)
  · intro h A B f g hrel
    by_contra hne
    exact h ⟨A, B, f, g, hne, hrel⟩

/-! ## 7. Correct small hom model: the 2-isomorphism quotient inside model homs -/

/-- The Type-0 carrier of the 2-isomorphism quotient of cover maps, realised as
a subtype of the model scheme morphisms.  This is the small hom family that
matches the actual cover category. -/
noncomputable def S1766QuotSmallCarrier (A B : S1728Cover) : Type :=
  Set.range (S1766QuotAct A B)

/-- The 2-isomorphism quotient of cover maps is equivalent to the Type-0
carrier S1766QuotSmallCarrier.  This is the correct small model for hom
types: homs are 2-isomorphism classes, not raw cover maps. -/
noncomputable def S1766QuotSmallEquiv (A B : S1728Cover) :
    Quot (fun f g : S1728CoverMap A B => S1728CoverMapRel f g) ≃
      S1766QuotSmallCarrier A B :=
  Equiv.ofInjective (S1766QuotAct A B) (S1766QuotAct_injective A B)

/-! ## 8. The commutes field is a subsingleton -/

/-- Strong transformations into a representable etale stack have subsingleton
modification types: every component lands in a discrete category. -/
theorem S1766_modification_subsingleton
    {W : Iut.EtaleStackPseudofunctor S1726K} {S : Iut.SchemeOverField S1726K}
    (eta theta : Pseudofunctor.StrongTrans W (S1766Y S)) :
    Subsingleton (eta ⟶ theta) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- The 2-cell comparing a cover map with the structure maps is unique, since
the target stack is representable.  Hence a cover map is determined by its
underlying strong transformation. -/
theorem S1766_commutes_subsingleton (A B : S1728Cover)
    (f : S1728CoverMap A B) :
    Subsingleton (Iso (Pseudofunctor.StrongTrans.vcomp f.map B.map) A.map) := by
  haveI h1 : Subsingleton
      (Pseudofunctor.StrongTrans.vcomp f.map B.map ⟶ A.map) :=
    S1766_modification_subsingleton _ _
  haveI h2 : Subsingleton
      (A.map ⟶ Pseudofunctor.StrongTrans.vcomp f.map B.map) :=
    S1766_modification_subsingleton _ _
  constructor
  intro e1 e2
  apply Iso.ext
  exact Subsingleton.elim _ _

/-- Cover maps are determined by their underlying strong transformation. -/
theorem S1766_coverMap_ext (A B : S1728Cover) {f g : S1728CoverMap A B}
    (h : f.map = g.map) : f = g := by
  cases f with
  | mk fmap fcomm =>
  cases g with
  | mk gmap gcomm =>
    dsimp only at h
    subst h
    haveI : Subsingleton (Iso
        (Pseudofunctor.StrongTrans.vcomp fmap B.map) A.map) :=
      S1766_commutes_subsingleton A B ⟨fmap, fcomm⟩
    congr 1
    exact Subsingleton.elim _ _

/-- Equivalently, R2a is the statement that no two distinct strong
transformations between cover sources are 2-isomorphic. -/
theorem S1766_coverMapDiscrete_iff :
    S1766CoverMapDiscrete ↔
      ∀ (A B : S1728Cover) (f g : S1728CoverMap A B),
        Nonempty (f.map ≅ g.map) → f.map = g.map := by
  constructor
  · intro h A B f g hrel
    exact congrArg (fun x : S1728CoverMap A B => x.map) (h A B f g hrel)
  · intro h A B f g hrel
    exact S1766_coverMap_ext A B (h A B f g hrel)

/-! ## 9. Checks and axiom audit -/

#check S1766Phi
#check S1766_act_def
#check S1766_modelMap_eq_iff_phi_iso
#check S1766_lift_toSource
#check S1766_phi_comp_toSource_iso
#check S1766_phi_iso_of_map_iso
#check S1766_map_iso_of_phi_iso
#check S1766_act_eq_iff_coverMapRel
#check S1766CanonicalAct_eq_iff_coverMapRel
#check S1766QuotAct
#check S1766QuotAct_injective
#check S1766CoverMapDiscrete
#check S1766_raw_injective_iff_discrete
#check S1766_raw_injective_of_discrete
#check S1766RawInjectivityExactMissing
#check S1766RawInjectivityExactMissing_iff
#check S1766ActualCounterexample
#check S1766_counterexample
#check S1766_collision
#check S1766_not_injective_iff_actualCounterexample
#check S1766_injective_iff_no_actualCounterexample
#check S1766QuotSmallCarrier
#check S1766QuotSmallEquiv
#check S1766_modification_subsingleton
#check S1766_commutes_subsingleton
#check S1766_coverMap_ext
#check S1766_coverMapDiscrete_iff

#print axioms S1766_act_def
#print axioms S1766_modelMap_eq_iff_phi_iso
#print axioms S1766_lift_toSource
#print axioms S1766_phi_comp_toSource_iso
#print axioms S1766_phi_iso_of_map_iso
#print axioms S1766_map_iso_of_phi_iso
#print axioms S1766_act_eq_iff_coverMapRel
#print axioms S1766CanonicalAct_eq_iff_coverMapRel
#print axioms S1766QuotAct
#print axioms S1766QuotAct_injective
#print axioms S1766_raw_injective_iff_discrete
#print axioms S1766_raw_injective_of_discrete
#print axioms S1766RawInjectivityExactMissing_iff
#print axioms S1766_counterexample
#print axioms S1766_collision
#print axioms S1766_not_injective_iff_actualCounterexample
#print axioms S1766_injective_iff_no_actualCounterexample
#print axioms S1766QuotSmallEquiv
#print axioms S1766_modification_subsingleton
#print axioms S1766_commutes_subsingleton
#print axioms S1766_coverMap_ext
#print axioms S1766_coverMapDiscrete_iff

end LeanFormal.IUT.XiFPaper.S1766CanonicalModelInjectivityActual
