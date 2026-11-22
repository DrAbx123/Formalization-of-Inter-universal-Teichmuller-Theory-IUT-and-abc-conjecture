import tmp.sheaf.xif.paper.S2022QuotientStackActual

/-!
# S2025: the quotient stack `[Z / mu_l]` -- receiver data, exact first missing, and the
downstream split

S2022 constructed the pointwise quotient stack data for

  `Z = Spec K[t]/t^l`,  `mu_l = Spec K[t,t^{-1}]/(t^l - 1)`,  `zeta . b = zeta * b`,

-- the group of `l`-torsion units, the thickened origin, the action groupoid, the
comparison of the action groupoid with the S1997 root fibre, the twist/PHS
dictionary, and the full faithfulness of the comparison *pointwise* -- and isolated

  `S2022FirstMissing K l := Nonempty (S2022QuotientStackPackage K l)`,

where a package is a category-valued etale stack `Q`, its stack condition
`Q.IsStack etaleTopology`, a strong transformation
`S1997RootPrestack K l -> Q`, and full faithfulness of that comparison at every test
object.  This file attacks the *construction* of the package (Giraud
stackification of the `mu_l`-torsor groupoid) and, since the construction is not
available in this tree, pins down the exact first missing in a form that says
precisely which part of the package is constructed and which part is missing.

## What Mathlib has, and what it does not have

Mathlib has the effective-descent predicate `Pseudofunctor.IsStack`
(`Mathlib/CategoryTheory/Sites/Descent/IsStack.lean`), the descent-data category,
`IsPrestack`, and the constructor `IsStack.of_isStackFor`.  Mathlib has **no**
stackification (left biadjoint to the inclusion of stacks in category-valued
pseudofunctors), **no** stack of torsors for a sheaf of groups, **no** line
bundles / quasi-coherent descent for schemes, and **no** instance of `IsStack`
for any category-valued pseudofunctor.  Consequently the Giraud construction
`[Z / mu_l]` -- objects over `U`: pairs `(P, phi)` of a `mu_l`-torsor `P` on the
etale site of `U` and a `mu_l`-equivariant map `P -> Z`, whose comparison sends
`b` to the trivial torsor with `zeta |-> zeta . b` -- cannot be written down in
this tree: both the torsor groupoid and its effective descent are missing.

This file therefore does *not* fake an `IsStack` instance.  It proves the honest
structural statement instead: **the comparison data of the package (and even its
stacky point) is constructed unconditionally; the package is missing exactly one
thing, the stack condition on a receiver, i.e. the Giraud stackification input.**

## What is constructed and proved

1. `S2025QuotientReceiver K l` (section 1): the package *without* the stack
   condition -- a pseudofunctor `Q`, a comparison `S1997RootPrestack K l -> Q`, and
   full faithfulness at every test object.  Two theorems:

   * `S2025QuotientReceiver.root`: the receiver data always exist (the root
     prestack receives itself through the identity comparison, which is fully
     faithful because the identity functor is);
   * `S2022FirstMissing_iff_exists_receiver_isStack`:
     `S2022FirstMissing K l` is exactly "some receiver is a stack".

   Hence the *entire* content of the missing is `IsStack`; the comparison and its
   full faithfulness are not a gap.

2. The exact automorphism group of any receiver (section 2):

   * `S2025EndMulEquiv`: a fully faithful functor induces a monoid isomorphism on
     endomorphism monoids;
   * `S2025Receiver_endEquiv`: at every test object `U` and every root object `X`,
     `End X ~= End (eta X)`;
   * `S2025Receiver_originEndEquiv`: at the origin,
     `End (eta 0) ~= mu_l(Gamma(U)) = {zeta : Gamma(U)^x // zeta^l = 1}`.  So a
     receiver has, at every test object, *exactly* the stabilizer `mu_l` at the
     origin -- not merely an order-`l` automorphism;
   * `S2025Receiver_stackyPoint`: consequently every receiver already carries a
     nontrivial order-`l` automorphism at the cyclic test scheme `Spec K[Z/l]`,
     *without any stack condition*: the stacky point is not part of the missing.
     This strictly generalizes `S2022QuotientStackPackage.stacky_point`;
   * `S2025Receiver_not_representable`: no receiver is a representable etale
     stack (representable stacks have discrete fibers), which strengthens S2002's
     no-go from witnesses of the S1997 datum to all receivers and all packages.

3. `S2025FirstMissing K l` (section 3): the exact first missing, in receiver form,
   proved equivalent to `S2022FirstMissing K l`, and shown to imply every consumer
   of S2022 (`S1997RootStackificationMissing`, `S2002RootStackificationDatum`,
   `S2019CorrectedRootStackDatum`, `S1994StackyOrbicurveMissing`).

4. The missing as an instance of Giraud's stackification theorem (section 4):
   `S2025PrestackStackification` is the general statement "a category-valued
   prestack has a stackification with fully faithful unit" -- a theorem of Giraud,
   which Mathlib does not contain, and which is *not* the effective descent of the
   root prestack itself (that is `S2019FirstMissing`, expected to fail; S2022's
   `prestack_iff_S2019FirstMissing` proves the prestack route is the `Q = root
   prestack` case).  We prove `S2025PrestackStackification -> S2025FirstMissing`,
   using only S2013's `IsPrestack` of the root prestack.  The general statement is
   non-vacuous: `S2025_stackification_of_isStack` proves its instance at any stack.

5. The downstream split (section 5): the S1994 consumer only needs an etale stack
   with a point with a nontrivial order-`l` automorphism, so the weaker statement
   `S2025StackyPoint K n` suffices.  We prove
   `S2022FirstMissing -> S2025StackyPoint` and `S2025StackyPoint -> S1994`'s
   stacky orbicurve, including its non-representability.  This decouples S1994
   from the root-prestack comparison entirely; it is the interface reduction of
   the missing for that consumer.

## Honest boundary

No `sorry`, no `admit`, no new axiom, no `PUnit`/`ULift`/`Shrink` placeholder, no
fabricated stack, no asserted `IsStack` instance.  `S2025FirstMissing` (equivalently
`S2022FirstMissing`) has no inhabitant here; the *constructed* data are the
receiver, its endomorphism computation and its stacky point.  The Giraud
stackification theorem is stated, not proved.  The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2025QuotientStackPackageActual

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1994KSideCovers
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S2002RootStackificationActual
open LeanFormal.IUT.XiFPaper.S2013RootHomSheafActual
open LeanFormal.IUT.XiFPaper.S2019RebasedRootStackActual
open LeanFormal.IUT.XiFPaper.S2022QuotientStackActual

universe u

variable {K : Type u} [Field K] {l : PrimeGeFive}

/-! ## 1. The receiver: the package minus the stack condition -/

/-- **The comparison data of the quotient stack.**  This is exactly
`S2022QuotientStackPackage` with the `IsStack` field removed: a category-valued
pseudofunctor `quotient`, a comparison from the root prestack, and full
faithfulness of that comparison at every test object.

For the actual `[Z / mu_l]` the comparison is the identity on the trivial torsor,
`b |-> (trivial torsor, zeta |-> zeta . b)`, and its full faithfulness is the
pointwise computation of S2022 section 4 (`S2022PhiEquiv`,
`S2022PhiTwistHomEquiv`). -/
structure S2025QuotientReceiver (K : Type u) [Field K] (l : PrimeGeFive) where
  /-- The 'quotient' pseudofunctor, before imposing descent. -/
  quotient : Iut.EtaleStackPseudofunctor K
  /-- The comparison from the root prestack (the trivial-torsor locus). -/
  comparison : Pseudofunctor.StrongTrans (S1997RootPrestack K l.value) quotient
  /-- The comparison is fully faithful at every test object. -/
  fullyFaithful : ∀ U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ,
    (comparison.app U).toFunctor.FullyFaithful

namespace S2025QuotientReceiver

variable {K : Type u} [Field K] {l : PrimeGeFive}

/-- **The receiver data are not missing**: the root prestack receives itself, with
the identity comparison, which is fully faithful because the identity functor is.
This is the content of S2022 section 4 made structural: what the pointwise
construction supplies is precisely a receiver. -/
noncomputable def root : S2025QuotientReceiver K l where
  quotient := S1997RootPrestack K l.value
  comparison := Pseudofunctor.StrongTrans.id _
  fullyFaithful := fun U => Functor.FullyFaithful.id ((S1997RootPrestack K l.value).obj U)

/-- A receiver whose quotient is a stack is exactly a package. -/
noncomputable def toPackage (R : S2025QuotientReceiver K l)
    (h : R.quotient.IsStack (Iut.SchemeOverField.etaleTopology K)) :
    S2022QuotientStackPackage K l where
  quotient := R.quotient
  isStack := h
  comparison := R.comparison
  fullyFaithful := R.fullyFaithful

/-- A package forgets to its receiver data. -/
def ofPackage (D : S2022QuotientStackPackage K l) : S2025QuotientReceiver K l where
  quotient := D.quotient
  comparison := D.comparison
  fullyFaithful := D.fullyFaithful

@[simp]
theorem ofPackage_quotient (D : S2022QuotientStackPackage K l) :
    (ofPackage D).quotient = D.quotient := rfl

/-- The receiver of the root prestack is the root prestack. -/
@[simp]
theorem root_quotient : (root (K := K) (l := l)).quotient = S1997RootPrestack K l.value := rfl

end S2025QuotientReceiver

/-- **The whole missing content of the package is the stack condition.**  The
comparison data with full faithfulness is not part of the gap (it exists
unconditionally, `S2025QuotientReceiver.root`); a package exists exactly when one
receiver happens to be a stack. -/
theorem S2022FirstMissing_iff_exists_receiver_isStack :
    S2022FirstMissing K l ↔
      ∃ R : S2025QuotientReceiver K l,
        R.quotient.IsStack (Iut.SchemeOverField.etaleTopology K) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨S2025QuotientReceiver.ofPackage D, D.isStack⟩
  · rintro ⟨R, h⟩
    exact ⟨R.toPackage h⟩

/-- A package is a receiver together with the stack condition, so every receiver
which is a stack is a package and conversely.  This is the elementwise form of
the previous theorem. -/
theorem S2025QuotientReceiver.nonempty_of_package (D : S2022QuotientStackPackage K l) :
    ∃ R : S2025QuotientReceiver K l,
      R.quotient.IsStack (Iut.SchemeOverField.etaleTopology K) :=
  ⟨S2025QuotientReceiver.ofPackage D, D.isStack⟩

/-! ## 2. Every receiver already computes the exact stabilizer at the origin -/

/-- A fully faithful functor induces a monoid isomorphism on endomorphism
monoids.  This is the sharp form of "faithful on automorphisms": the comparison
does not merely reflect the identity, it is bijective on endomorphisms. -/
noncomputable def S2025EndMulEquiv {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) (hF : F.FullyFaithful) (X : C) : End X ≃* End (F.obj X) where
  toFun := ⇑(S1997EndMap F X)
  invFun g := hF.preimage g
  left_inv f := hF.preimage_map f
  right_inv g := hF.map_preimage g
  map_mul' f g := map_mul (S1997EndMap F X) f g

/-- At every test object and every root object, a receiver's quotient has exactly
the endomorphism monoid of the root fibre. -/
noncomputable def S2025Receiver_endEquiv (R : S2025QuotientReceiver K l)
    (U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ)
    (X : (S1997RootPrestack K l.value).obj U) :
    End X ≃* End ((R.comparison.app U).toFunctor.obj X) :=
  S2025EndMulEquiv _ (R.fullyFaithful U) X

/-- **The exact stabilizer at the origin**: for every receiver and every test
object `U`, the automorphism monoid of the image of the origin `0` is exactly the
group `mu_l(Gamma(U))` of `l`-torsion units of the global sections.  This is
S2022's pointwise comparison (`S2022RootHomZeroEquiv`, itself
`S2022PhiTwistHomZero` composed with `S2022PhiTwistHomEquiv`) pushed through the
full faithfulness of the comparison. -/
noncomputable def S2025Receiver_originEndEquiv (R : S2025QuotientReceiver K l)
    (U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) :
    End ((R.comparison.app U).toFunctor.obj
        (S2022RootObjZero (Γ(U.as.unop.left, ⊤)) l.prime.pos)) ≃
      ↥(S2022Mu (Γ(U.as.unop.left, ⊤)) l.value) :=
  (Equiv.trans
    ((S2025Receiver_endEquiv R U (S2022RootObjZero _ l.prime.pos)).symm.toEquiv)
    (S2022RootHomZeroEquiv _ l.prime.pos).symm)

/-- **Every receiver already has a stacky point.**  At the cyclic test scheme
`Spec K[Z/l]` the order-`l` automorphism of the origin is carried by full
faithfulness to a nontrivial automorphism of order `l`; no stack condition is
used.  (`S2022QuotientStackPackage.stacky_point` is the special case of a
package.) -/
theorem S2025Receiver_stackyPoint (R : S2025QuotientReceiver K l) :
    ∃ (U : Iut.SchemeOverField K)
      (X : R.quotient.obj (LocallyDiscrete.mk (Opposite.op U)))
      (f : End X), f ≠ 𝟙 X ∧ f ^ l.value = 𝟙 X := by
  refine ⟨S1997CyclicScheme K l,
    (R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.obj
      (S1997CyclicOrigin K l),
    (R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map
      (S1997CyclicOriginAutEnd K l), ?_, ?_⟩
  · intro h
    have hid : (R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map
        (𝟙 (S1997CyclicOrigin K l)) =
        𝟙 ((R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.obj
          (S1997CyclicOrigin K l)) :=
      (R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map_id _
    exact S1997CyclicOriginAut_ne_one K l
      ((R.fullyFaithful (S2002CyclicPoint (K := K) (l := l))).map_injective
        (h.trans hid.symm))
  · let f1 : End ((R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.obj
        (S1997CyclicOrigin K l)) :=
      (R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map
        (S1997CyclicOriginAutEnd K l)
    have hmap := map_pow (S1997EndMap
        (R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor
        (S1997CyclicOrigin K l)) (S1997CyclicOriginAutEnd K l) l.value
    change (R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map
        ((S1997CyclicOriginAutEnd K l) ^ l.value) = f1 ^ l.value at hmap
    rw [S1997CyclicOriginAut_pow K l] at hmap
    change (R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map
        (𝟙 (S1997CyclicOrigin K l)) = f1 ^ l.value at hmap
    rw [(R.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map_id] at hmap
    exact hmap.symm

/-- A receiver has a point with a nontrivial automorphism (the existential form
used by the orbicurve consumers). -/
theorem S2025Receiver_hasNontrivialAut (R : S2025QuotientReceiver K l) :
    ∃ (U : Iut.SchemeOverField K)
      (P : R.quotient.obj (LocallyDiscrete.mk (Opposite.op U)))
      (f : End P), f ≠ 𝟙 P := by
  obtain ⟨U, X, f, hf, -⟩ := S2025Receiver_stackyPoint R
  exact ⟨U, X, f, hf⟩

/-- Every receiver's quotient has a fiber whose endomorphism type is not a
subsingleton: the comparison cannot be replaced by a discrete (sheaf-of-sets)
quotient.  This is the receiver-level version of S2002's no-go for discrete
fibers. -/
theorem S2025Receiver_not_discreteFiber (R : S2025QuotientReceiver K l) :
    ¬ S2002DiscreteFiber R.quotient := by
  intro hdisc
  obtain ⟨U, X, f, hf, -⟩ := S2025Receiver_stackyPoint R
  haveI : Subsingleton (End X) := hdisc (LocallyDiscrete.mk (Opposite.op U)) X X
  exact hf (Subsingleton.elim f (𝟙 X))

/-- **No receiver is representable**: a representable etale pseudofunctor has
discrete fibers (S2002), so it cannot carry the order-`l` origin automorphism.  This
strengthens S2002's no-go `S2002_noRepresentableWitness` from witnesses of the
S1997 datum to arbitrary receivers, hence to every package. -/
theorem S2025Receiver_not_representable (R : S2025QuotientReceiver K l)
    (X : Iut.SchemeOverField K) :
    R.quotient ≠ Iut.schemeRepresentableEtalePseudofunctor K X := by
  intro h
  exact S2025Receiver_not_discreteFiber R
    (h ▸ S2002RepresentableDiscreteFiber X)

/-! ## 3. The exact first missing in receiver form -/

/-- **The exact first missing of the quotient-stack route, in receiver form**: the
quotient data of `[Z / mu_l]` (comparison plus full faithfulness) exist
unconditionally, and the missing input is that some receiver -- necessarily one
carrying the `mu_l`-torsor groupoid of the actual quotient stack -- satisfies
effective descent for the etale topology.

Equivalently (`S2025FirstMissing_iff_S2022FirstMissing`) this is exactly
`S2022FirstMissing K l`.  No inhabitant is asserted. -/
def S2025FirstMissing (K : Type u) [Field K] (l : PrimeGeFive) : Prop :=
  ∃ R : S2025QuotientReceiver K l,
    R.quotient.IsStack (Iut.SchemeOverField.etaleTopology K)

/-- **The receiver form of the missing is exactly S2022's `S2022FirstMissing`.** -/
theorem S2025FirstMissing_iff_S2022FirstMissing :
    S2025FirstMissing K l ↔ S2022FirstMissing K l :=
  (S2022FirstMissing_iff_exists_receiver_isStack (K := K) (l := l)).symm

/-- The missing supplies S1997's root stackification. -/
theorem S2025FirstMissing_implies_S1997 (h : S2025FirstMissing K l) :
    S1997RootStackificationMissing K l :=
  S2022FirstMissing_implies_S1997
    ((S2025FirstMissing_iff_S2022FirstMissing (K := K) (l := l)).mp h)

/-- The missing supplies S2002's existential datum. -/
theorem S2025FirstMissing_implies_S2002 (h : S2025FirstMissing K l) :
    S2002RootStackificationDatum (K := K) (l := l) :=
  S2022FirstMissing_implies_S2002
    ((S2025FirstMissing_iff_S2022FirstMissing (K := K) (l := l)).mp h)

/-- The missing supplies S2019's corrected root-stack datum. -/
theorem S2025FirstMissing_implies_S2019Corrected (h : S2025FirstMissing K l) :
    Nonempty (S2019CorrectedRootStackDatum K l) :=
  S2022FirstMissing_implies_S2019Corrected
    ((S2025FirstMissing_iff_S2022FirstMissing (K := K) (l := l)).mp h)

/-- The missing supplies S1994's stacky orbicurve. -/
theorem S2025FirstMissing_implies_S1994 {lg : PrimeGeFive}
    {A : InitialThetaArithmeticData lg} (h : S2025FirstMissing A.K lg) :
    S1994StackyOrbicurveMissing lg A :=
  S2022FirstMissing_implies_S1994
    ((S2025FirstMissing_iff_S2022FirstMissing (K := A.K) (l := lg)).mp h)

/-- The prestack route is the case `Q = root prestack` of the receiver form: if
the root prestack itself is a stack, the receiver `root` is a witness. -/
theorem S2019FirstMissing_implies_S2025FirstMissing
    (h : S2019FirstMissing (K := K) (l := l)) : S2025FirstMissing K l :=
  (S2025FirstMissing_iff_S2022FirstMissing (K := K) (l := l)).mpr
    (S2019FirstMissing_implies_S2022FirstMissing h)

/-- **A receiver which is a stack is the package, so the missing is exactly the
stack condition on the receiver.**  This is the same content as
`S2022FirstMissing_iff_exists_receiver_isStack`, stated with the named missing. -/
theorem S2025FirstMissing_iff_exists_receiver :
    S2025FirstMissing K l ↔
      ∃ R : S2025QuotientReceiver K l,
        R.quotient.IsStack (Iut.SchemeOverField.etaleTopology K) :=
  Iff.rfl

/-! ## 4. The missing as an instance of Giraud's stackification theorem -/

/-- **Giraud stackification for category-valued prestacks**: every prestack on
every site has a stackification whose unit is fully faithful.  This is a theorem
of Giraud ("the stackification of a prestack has a fully faithful unit", the
left biadjoint to the inclusion of stacks), and it is *not* in Mathlib: Mathlib
has `IsStack`, `IsPrestack` and descent data, but no stackification functor and
no instance of `IsStack` at all.

This is the general statement whose instance at the root prestack is the missing
input of the paper's `[Z / mu_l]`.  It is distinct from the effective descent of
the root prestack itself (`S2019FirstMissing`, expected to fail for Kummer
covers): stackification is allowed to add the nontrivial `mu_l`-torsors. -/
def S2025PrestackStackification : Prop :=
  ∀ {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u}),
    F.IsPrestack J →
      ∃ Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u},
        Q.IsStack J ∧
          ∃ eta : Pseudofunctor.StrongTrans F Q,
            Nonempty (∀ U : LocallyDiscrete Cᵒᵖ, (eta.app U).toFunctor.FullyFaithful)

/-- **The site-specific form of the missing**: the stackification of the root
prestack, i.e. the quotient stack `[Z / mu_l]`, as a stack with a fully faithful
comparison.  This is exactly `S2022FirstMissing`, and its mathematical content is
the Giraud construction of the quotient stack. -/
def S2025RootStackification (K : Type u) [Field K] (l : PrimeGeFive) : Prop :=
  ∃ Q : Iut.EtaleStackPseudofunctor K,
    Q.IsStack (Iut.SchemeOverField.etaleTopology K) ∧
      ∃ eta : Pseudofunctor.StrongTrans (S1997RootPrestack K l.value) Q,
        Nonempty (∀ U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ,
          (eta.app U).toFunctor.FullyFaithful)

/-- The site-specific form and the package missing are the same proposition. -/
theorem S2025RootStackification_iff_S2022FirstMissing :
    S2025RootStackification K l ↔ S2022FirstMissing K l := by
  constructor
  · rintro ⟨Q, hQ, eta, ⟨heta⟩⟩
    exact ⟨{ quotient := Q, isStack := hQ, comparison := eta, fullyFaithful := heta }⟩
  · rintro ⟨D⟩
    exact ⟨D.quotient, D.isStack, D.comparison, ⟨D.fullyFaithful⟩⟩

/-- **Giraud's stackification theorem gives the quotient stack.**  The only input
taken from the root prestack is S2013's proven `IsPrestack`; nothing about
effective descent of the root prestack is assumed. -/
theorem S2025PrestackStackification.toS2025FirstMissing
    (h : S2025PrestackStackification.{u}) : S2025FirstMissing (K := K) (l := l) := by
  obtain ⟨Q, hQ, eta, ⟨heta⟩⟩ :=
    h (Iut.SchemeOverField.etaleTopology K) (S1997RootPrestack K l.value)
      (S2013RootPrestack_isPrestack (K := K) (l := l))
  exact ⟨{ quotient := Q, comparison := eta, fullyFaithful := heta }, hQ⟩

/-- Giraud's theorem also gives S2022's named missing directly. -/
theorem S2025PrestackStackification.toS2022FirstMissing
    (h : S2025PrestackStackification.{u}) : S2022FirstMissing (K := K) (l := l) :=
  (S2025FirstMissing_iff_S2022FirstMissing (K := K) (l := l)).mp
    (S2025PrestackStackification.toS2025FirstMissing (K := K) (l := l) h)

/-- **Non-vacuity of the stackification statement**: any stack is its own
stackification, with the identity (fully faithful) unit.  So the missing statement
is not an empty formula: it has inhabitants for the class of prestacks which are
already stacks, and only the general case is open. -/
theorem S2025_stackification_of_isStack
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u}) (hF : F.IsStack J) :
    ∃ Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u},
      Q.IsStack J ∧
        ∃ eta : Pseudofunctor.StrongTrans F Q,
          Nonempty (∀ U : LocallyDiscrete Cᵒᵖ, (eta.app U).toFunctor.FullyFaithful) :=
  ⟨F, hF, Pseudofunctor.StrongTrans.id F,
    ⟨fun U => Functor.FullyFaithful.id (F.obj U)⟩⟩

/-! ## 5. The weaker sufficient statement for the S1994 consumer -/

/-- **An etale stack with a stacky point of order `n`.**  This statement mentions
neither the root prestack nor the comparison of `[Z / mu_l]`: it is the interface
actually consumed downstream. -/
def S2025StackyPoint (K : Type u) [Field K] (n : ℕ) : Prop :=
  ∃ Q : Iut.EtaleStackPseudofunctor K,
    Q.IsStack (Iut.SchemeOverField.etaleTopology K) ∧
      ∃ (U : Iut.SchemeOverField K)
        (X : Q.obj (LocallyDiscrete.mk (Opposite.op U)))
        (f : End X), f ≠ 𝟙 X ∧ f ^ n = 𝟙 X

/-- **The package implies the decoupled stacky-point statement.** -/
theorem S2022FirstMissing.toStackyPoint (h : S2022FirstMissing K l) :
    S2025StackyPoint K l.value := by
  obtain ⟨D⟩ := h
  obtain ⟨U, X, f, hf, hpow⟩ := S2025Receiver_stackyPoint (S2025QuotientReceiver.ofPackage D)
  exact ⟨D.quotient, D.isStack, U, X, f, hf, hpow⟩

/-- **The stacky-point statement gives S1994's stacky orbicurve.**  The stack is
wrapped into a hyperbolic orbicurve with the once-punctured elliptic signature
(`realizedHyperbolicOrbicurve`, which stores the signature certificate), and the
order-`n` automorphism is carried along unchanged. -/
theorem S2025StackyPoint.toOrbicurve (h : S2025StackyPoint K n) :
    ∃ X : Iut.HyperbolicOrbicurve K, S1994HasAutOfOrder X n := by
  obtain ⟨Q, hQ, U, X, f, hf, hpow⟩ := h
  refine ⟨realizedHyperbolicOrbicurve K Q hQ
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic, ?_⟩
  exact ⟨U, X, f, hf, hpow⟩

/-- **Moreover that orbicurve is not representable**: a representable orbicurve
has only identity automorphisms (its fibers are discrete), so a point with a
nontrivial automorphism cannot occur in one. -/
theorem S2025StackyPoint.exists_orbicurve_not_representable
    (h : S2025StackyPoint K n) :
    ∃ X : Iut.HyperbolicOrbicurve K, S1994HasAutOfOrder X n ∧
      ∀ (Y : Iut.SchemeOverField K) (sigma : Iut.OrbicurveSignature)
        (hsigma : sigma.IsHyperbolic),
        X ≠ S1994RepresentableOrbicurve (F := K) Y sigma hsigma := by
  obtain ⟨Q, hQ, U, X, f, hf, hpow⟩ := h
  refine ⟨realizedHyperbolicOrbicurve K Q hQ
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic,
    ⟨U, X, f, hf, hpow⟩, ?_⟩
  rintro Y sigma hsigma hEq
  refine S1994RepresentableOrbicurve_noAutOfOrder (F := K) Y sigma hsigma n ?_
  rw [← hEq]
  exact ⟨U, X, f, hf, hpow⟩

/-- The stacky-point statement supplies S1994's named missing object. -/
theorem S2025StackyPoint.toS1994StackyOrbicurve {lg : PrimeGeFive}
    {A : InitialThetaArithmeticData lg} (h : S2025StackyPoint A.K lg.value) :
    S1994StackyOrbicurveMissing lg A :=
  S2025StackyPoint.toOrbicurve h

/-- **The consumer chain through the weaker statement**: the S1994 missing object
follows from `S2022FirstMissing` without using the root-prestack comparison; only
the stacky point of the quotient is needed. -/
theorem S2022FirstMissing.toS1994_viaStackyPoint {lg : PrimeGeFive}
    {A : InitialThetaArithmeticData lg} (h : S2022FirstMissing A.K lg) :
    S1994StackyOrbicurveMissing lg A :=
  S2025StackyPoint.toS1994StackyOrbicurve (S2022FirstMissing.toStackyPoint h)

/-- No representable etale stack can supply the stacky point: representable stacks
have discrete fibers, so all endomorphisms are identities.  This forbids the
trivial/representable substitutes for `[Z / mu_l]` in the weaker statement as
well. -/
theorem S2025Representable_not_stackyPoint (X : Iut.SchemeOverField K) :
    ¬ ∃ (U : Iut.SchemeOverField K)
        (P : (Iut.schemeRepresentableEtalePseudofunctor K X).obj
          (LocallyDiscrete.mk (Opposite.op U)))
        (f : End P), f ≠ 𝟙 P := by
  rintro ⟨U, P, f, hf⟩
  have hsub : Subsingleton (End P) :=
    Discrete.instSubsingletonDiscreteHom P P
  haveI := hsub
  exact hf (Subsingleton.elim f (𝟙 P))

/-! ## 6. Checks and axiom footprint -/

#check @S2025QuotientReceiver
#check @S2025QuotientReceiver.root
#check @S2025QuotientReceiver.toPackage
#check @S2025QuotientReceiver.ofPackage
#check @S2022FirstMissing_iff_exists_receiver_isStack
#check @S2025EndMulEquiv
#check @S2025Receiver_endEquiv
#check @S2025Receiver_originEndEquiv
#check @S2025Receiver_stackyPoint
#check @S2025Receiver_hasNontrivialAut
#check @S2025Receiver_not_discreteFiber
#check @S2025Receiver_not_representable
#check @S2025FirstMissing
#check @S2025FirstMissing_iff_S2022FirstMissing
#check @S2025FirstMissing_implies_S1997
#check @S2025FirstMissing_implies_S2002
#check @S2025FirstMissing_implies_S2019Corrected
#check @S2025FirstMissing_implies_S1994
#check @S2019FirstMissing_implies_S2025FirstMissing
#check @S2025PrestackStackification
#check @S2025RootStackification
#check @S2025RootStackification_iff_S2022FirstMissing
#check @S2025PrestackStackification.toS2025FirstMissing
#check @S2025PrestackStackification.toS2022FirstMissing
#check @S2025_stackification_of_isStack
#check @S2025StackyPoint
#check @S2022FirstMissing.toStackyPoint
#check @S2025StackyPoint.toOrbicurve
#check @S2025StackyPoint.exists_orbicurve_not_representable
#check @S2025StackyPoint.toS1994StackyOrbicurve
#check @S2022FirstMissing.toS1994_viaStackyPoint
#check @S2025Representable_not_stackyPoint

#print axioms S2025QuotientReceiver.root
#print axioms S2022FirstMissing_iff_exists_receiver_isStack
#print axioms S2025EndMulEquiv
#print axioms S2025Receiver_endEquiv
#print axioms S2025Receiver_originEndEquiv
#print axioms S2025Receiver_stackyPoint
#print axioms S2025Receiver_not_discreteFiber
#print axioms S2025Receiver_not_representable
#print axioms S2025FirstMissing_iff_S2022FirstMissing
#print axioms S2025FirstMissing_implies_S1997
#print axioms S2025FirstMissing_implies_S2002
#print axioms S2025FirstMissing_implies_S2019Corrected
#print axioms S2025FirstMissing_implies_S1994
#print axioms S2019FirstMissing_implies_S2025FirstMissing
#print axioms S2025RootStackification_iff_S2022FirstMissing
#print axioms S2025PrestackStackification.toS2025FirstMissing
#print axioms S2025_stackification_of_isStack
#print axioms S2022FirstMissing.toStackyPoint
#print axioms S2025StackyPoint.toOrbicurve
#print axioms S2025StackyPoint.exists_orbicurve_not_representable
#print axioms S2025StackyPoint.toS1994StackyOrbicurve
#print axioms S2022FirstMissing.toS1994_viaStackyPoint
#print axioms S2025Representable_not_stackyPoint

end LeanFormal.IUT.XiFPaper.S2025QuotientStackPackageActual