/-
# S1832: pullbacks in the actual S1728 finite-etale cover category

## The question

S1762 closed the terminal/identity field of the actual S1728 category

  S1728ActualCategory11 : Category.{1,1} (OrbicurveFiniteEtaleCover S1726Orbicurve)

(the 2-isomorphism quotient of the actual finite-etale cover maps) but left

  S1762PullbackObligationActual  =  HasPullbacks S1728ActualCategory11

open, with the geometric reading "the bicategorical fibre product of the two
cover source stacks over the common cover, a two-pullback witness for its
defining square, finite etaleness of the two projections, and the induced
universal property in the 2-isomorphism quotient", together with the remark
that "the two-pullback witness alone does not give the quotient-category limit;
that is the quotient universal-property half which is also missing".

## What is proved here

1. The quotient universal-property half is not missing.  For a cospan
   f : A -> C, g : B -> C of *actual* cover maps (not quotient classes) we
   introduce the exact bicategorical pullback datum S1832TwoPullback f g:

   * a cover "apex" with cover maps toA : apex -> A and toB : apex -> B,
   * a 2-isomorphism "commutes" making the square 2-commute,
   * a lift of every pseudo-cone ("lift"),
   * the two comparison 2-isomorphisms of the lift ("liftToA", "liftToB"),
   * uniqueness of the lift up to 2-isomorphism ("uniq").

   From this data alone, S1832HasLimit_of_twoPullback constructs a genuine
   Mathlib limit cone in the 2-isomorphism quotient category: the cone point is
   the apex, the legs are the classes of toA and toB, and the lifting morphism
   of a cone is the class of the bicategorical lift of the pseudo-cone obtained
   from the cone by Quot.out and Quot.eqvGen_exact.  Hence
   S1832HasPullback_of_twoPullback, and for a whole family of cospans
   S1832HasPullbacks_of_squares, which discharges S1762's pullback obligation
   from bicategorical fibre products.  So the quotient universal property is
   free: it does not have to be assumed or constructed separately.

2. The exact form of the obligation.  Conversely
   (S1832TwoPullbackOfHasPullback) a limit cone in the quotient category
   produces S1832TwoPullback f g for the given cospan, by taking Quot.out of the
   two legs and of the lifting morphisms and reading the 2-isomorphisms off the
   equalities in the quotient.  Hence

     S1832FirstMissingPullback  <->  HasPullbacks S1728ActualCategory11,

   where S1832FirstMissingPullback is the statement that *every* cospan of
   actual cover maps admits a bicategorical fibre-product cover.  This is the
   precise form of the remaining geometric input, and it is not weakened by any
   quotient bookkeeping.

3. Unconditional instances.  For the cospans whose second (resp. first) leg is
   the identity cover map S1641CoverMapId, the apex is the other cover and all
   coherence 2-cells are the bicategory unitors; the missing datum is inhabited
   (S1832TwoPullback_id_right, S1832TwoPullback_id_left), and so those cospans
   have actual pullbacks in the quotient category (S1832HasPullback_id_right,
   S1832HasPullback_id_left).  This shows that the hypothesis of item 1 and the
   statement of item 2 are not vacuous, and it uses the identity API of S1762
   (the identity cover map of S1641 with its unitor comparison).

4. Consumers.  S1832PullbackObligationActual_of_squares feeds S1762's literal
   pullback field; S1832HasFiniteLimitsActual feeds S1762's finite-limit field
   (S1762HasFiniteLimits_of_pullbacks, whose terminal input is already closed);
   S1832PreGaloisCategoryOfSquares assembles the actual PreGaloisCategory from
   the bicategorical fibre-product statement together with S1762's three
   remaining fields.

## What is *not* constructed, and why

S1832FirstMissingPullback is not inhabited here.  By item 2 it is equivalent to
HasPullbacks itself, so any inhabitant would close S1762's pullback field; no
such construction is present in the tree.  The genuine geometric inputs that an
inhabitant needs, none of which is available, are:

* the pseudopullback (iso-comma) stack of A.source -> C.source <- B.source as an
  object of the bicategory of etale stacks, including its descent (IsStack)
  condition, i.e. a new category-valued pseudofunctor on the whole etale site,
  not only its fibres;
* a structure map from that stack to X.stack and a proof that it is
  *representably finite etale*: this needs base-change presentations of the two
  projections and stability of finite etaleness under pullback and composition.
  Note that OrbicurveFiniteEtaleCoverMap itself carries *no* finite-etale
  condition on its underlying strong transformation, so even "a map between
  finite-etale covers is finite etale" is not available in the tree;
* the universal property at the level of strong transformations: the lift of
  every pseudo-cone with its two comparison 2-cells, and uniqueness of the lift
  up to 2-isomorphism.  The seven recorded fields of
  EtalePseudofunctorSquare.TwoPullbackWitness do *not* suffice: S1801 exhibits a
  square with a recorded witness whose cone comparison is not essentially
  surjective, and S1827 records the same missing half for the recorded
  identity-point square of a cover.  This is why S1832TwoPullback carries
  "lift" together with "uniq", rather than only the recorded fields.

## Honest boundary

No sorry, no new axiom, no Shrink, ULift or PUnit, and no fake object: the
quotient category and its limits are the actual ones (Mathlib
PullbackCone/IsLimit at S1728's Category.{1,1} instance), and the bicategorical
data are actual cover maps and actual 2-isomorphisms of strong transformations.
The only axioms are propext, Classical.choice and Quot.sound; see the
#print axioms block at the end.  HasPullbacks on the actual category is *not*
asserted; the exact first missing statement is S1832FirstMissingPullback, proved
equivalent to it.

Universe note: the statement is made for the S1728 quotient category
S1728ActualCategory11 : Category.{1,1}.  The S1809 small-hom category
S1809CoverCategory01 is equivalent to it (S1809ComparisonFunctor_isEquivalence),
so the same geometric input is the only missing datum there; the transport of
the limit statement along that equivalence is not formalised here.
-/

import tmp.sheaf.xif.paper.S1762CoverLimitsActual
import tmp.sheaf.xif.paper.S1809SmallCarrierCategoryActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual
open LeanFormal.IUT.XiFPaper.S1809SmallCarrierCategoryActual

/-! ## 1. Quotient bookkeeping: classes versus 2-isomorphisms -/

/-- The 2-isomorphism relation on actual cover maps between two fixed covers. -/
abbrev S1832Rel (A B : S1728Cover) : S1728CoverMap A B → S1728CoverMap A B → Prop :=
  fun f g => S1728CoverMapRel f g

/-- The class of an actual cover map in the 2-isomorphism quotient category,
with its type made explicit so that cospans elaborate without unfolding
S1728CoverMapClass. -/
abbrev S1832Q {A B : S1728Cover} (f : S1728CoverMap A B) : A ⟶ B :=
  Quot.mk (S1832Rel A B) f

/-- The chosen representative of a class represents it. -/
theorem S1832Q_out {A B : S1728Cover} (q : A ⟶ B) : S1832Q (Quot.out q) = q :=
  Quot.out_eq q

/-- An equality of 2-isomorphism classes of cover maps is a 2-isomorphism of
the underlying strong transformations.  This uses that the relation
S1728CoverMapRel is already an equivalence relation, so its equivalence closure
is itself. -/
theorem S1832RelOfQuotEq {A B : S1728Cover} {f g : S1728CoverMap A B}
    (h : S1832Q f = S1832Q g) : S1728CoverMapRel f g :=
  S1809EqvGen_to_rel (S1728CoverMapRel_equivalence A B) (Quot.eqvGen_exact h)

/-- Composition in the 2-isomorphism quotient category is the class of the
actual composite cover map. -/
theorem S1832QuotComp {A B C : S1728Cover} (f : S1728CoverMap A B)
    (g : S1728CoverMap B C) :
    (S1832Q f ≫ S1832Q g : A ⟶ C) = S1832Q (S1641CoverMapComp f g) := by
  change Quot.map₂ (fun f g => S1641CoverMapComp f g)
      (fun _ _ _ hg => S1728CoverMapRel_comp_right _ hg)
      (fun _ _ _ hf => S1728CoverMapRel_comp_left _ hf)
      (Quot.mk _ f) (Quot.mk _ g) = Quot.mk _ (S1641CoverMapComp f g)
  exact Quot.map₂_mk ..

/-- Composition on the left, for an arbitrary class identified with the class of
an actual cover map. -/
theorem S1832QuotCompMk {A B C : S1728Cover} (f : S1728CoverMap A B)
    (g : S1728CoverMap B C) {q : A ⟶ B} (hf : q = S1832Q f) :
    (q ≫ S1832Q g : A ⟶ C) = S1832Q (S1641CoverMapComp f g) := by
  rw [hf]
  exact S1832QuotComp f g

/-- Composition on the right, for an arbitrary class identified with the class
of an actual cover map. -/
theorem S1832QuotCompMk' {A B C : S1728Cover} (f : S1728CoverMap A B)
    (g : S1728CoverMap B C) {q : B ⟶ C} (hq : q = S1832Q g) :
    (S1832Q f ≫ q : A ⟶ C) = S1832Q (S1641CoverMapComp f g) := by
  rw [hq]
  exact S1832QuotComp f g

/-- The 2-commutativity 2-cell of a cone in the quotient category, read off from
chosen representatives of its two legs. -/
noncomputable def S1832ConeCommutesOfEq {W A B C : S1728Cover}
    {f : S1728CoverMap A C} {g : S1728CoverMap B C}
    (u : W ⟶ A) (v : W ⟶ B) (h : u ≫ S1832Q f = v ≫ S1832Q g) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Quot.out u).map f.map)
      (Pseudofunctor.StrongTrans.vcomp (Quot.out v).map g.map) := by
  have h1 := S1832QuotCompMk (Quot.out u) f (S1832Q_out u).symm
  have h2 := S1832QuotCompMk (Quot.out v) g (S1832Q_out v).symm
  have hc : S1832Q (S1641CoverMapComp (Quot.out u) f) =
      S1832Q (S1641CoverMapComp (Quot.out v) g) := by
    calc S1832Q (S1641CoverMapComp (Quot.out u) f) = u ≫ S1832Q f := h1.symm
      _ = v ≫ S1832Q g := h
      _ = S1832Q (S1641CoverMapComp (Quot.out v) g) := h2
  exact (by simpa only [S1641CoverMapComp_map] using
    Classical.choice (S1832RelOfQuotEq hc))

/-- If the class of a composite of actual representatives equals the class of
another actual representative, the two underlying transformations are
2-isomorphic. -/
theorem S1832IsoOfCompEq {W A B : S1728Cover} (u₀ : S1728CoverMap W A)
    (v₀ : S1728CoverMap A B) (w₀ : S1728CoverMap W B)
    (h : S1832Q u₀ ≫ S1832Q v₀ = S1832Q w₀) :
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp u₀.map v₀.map) w₀.map) := by
  have h' : S1832Q (S1641CoverMapComp u₀ v₀) = S1832Q w₀ := by
    calc S1832Q (S1641CoverMapComp u₀ v₀) = S1832Q u₀ ≫ S1832Q v₀ :=
          (S1832QuotComp u₀ v₀).symm
      _ = S1832Q w₀ := h
  obtain ⟨e⟩ := S1832RelOfQuotEq h'
  exact ⟨by simpa only [S1641CoverMapComp_map] using e⟩

/-! ## 2. Bicategorical cones and the two-pullback datum -/

/-- A pseudo-cone over the cospan f : A -> C, g : B -> C of actual cover maps,
with apex a cover W: the two legs are actual cover maps and the square
2-commutes. -/
structure S1832Bicone {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (W : S1728Cover) where
  /-- The leg to the first cover. -/
  toA : S1728CoverMap W A
  /-- The leg to the second cover. -/
  toB : S1728CoverMap W B
  /-- The 2-commutativity of the square. -/
  commutes : Iso (Pseudofunctor.StrongTrans.vcomp toA.map f.map)
    (Pseudofunctor.StrongTrans.vcomp toB.map g.map)

/-- The bicategorical fibre product datum for the cospan f, g: a cover apex
whose square is a bicategorical pullback, expressed as the lift of every
pseudo-cone together with the two comparison 2-isomorphisms and uniqueness of
the lift up to 2-isomorphism.  This is exactly the strength of a limit of the
cospan in the 2-isomorphism quotient category (S1832FirstMissing_iff_hasPullbacks):
a lift for every pseudo-cone, unique up to 2-isomorphism.  It is strictly
stronger than the seven recorded fields of
EtalePseudofunctorSquare.TwoPullbackWitness, whose cone comparison need not be
essentially surjective (S1801, S1827). -/
structure S1832TwoPullback {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) where
  /-- The apex of the square, an actual finite-etale cover of X. -/
  apex : S1728Cover
  /-- The first projection. -/
  toA : S1728CoverMap apex A
  /-- The second projection. -/
  toB : S1728CoverMap apex B
  /-- The 2-commutativity of the square. -/
  commutes : Iso (Pseudofunctor.StrongTrans.vcomp toA.map f.map)
    (Pseudofunctor.StrongTrans.vcomp toB.map g.map)
  /-- The lift of a pseudo-cone. -/
  lift : ∀ (W : S1728Cover), S1832Bicone f g W → S1728CoverMap W apex
  /-- The comparison 2-isomorphism with the first leg. -/
  liftToA : ∀ (W : S1728Cover) (c : S1832Bicone f g W),
    Iso (Pseudofunctor.StrongTrans.vcomp (lift W c).map toA.map) c.toA.map
  /-- The comparison 2-isomorphism with the second leg. -/
  liftToB : ∀ (W : S1728Cover) (c : S1832Bicone f g W),
    Iso (Pseudofunctor.StrongTrans.vcomp (lift W c).map toB.map) c.toB.map
  /-- Uniqueness of the lift up to 2-isomorphism. -/
  uniq : ∀ (W : S1728Cover) (c : S1832Bicone f g W) (h : S1728CoverMap W apex),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp h.map toA.map) c.toA.map) →
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp h.map toB.map) c.toB.map) →
    Nonempty (Iso h.map (lift W c).map)

/-! ## 3. The quotient universal property: a two-pullback datum gives a limit
cone in the actual 2-isomorphism quotient category -/

section Main

variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}

/-- The pseudo-cone attached to a cone of the quotient category. -/
noncomputable def S1832BiconeOfCone (s : PullbackCone (S1832Q f) (S1832Q g)) :
    S1832Bicone f g s.pt where
  toA := Quot.out s.fst
  toB := Quot.out s.snd
  commutes := S1832ConeCommutesOfEq s.fst s.snd s.condition

/-- The two legs of that pseudo-cone, stated separately so that they can be
rewritten in the comparison 2-isomorphisms. -/
@[simp] theorem S1832BiconeOfCone_toA (s : PullbackCone (S1832Q f) (S1832Q g)) :
    (S1832BiconeOfCone s).toA = Quot.out s.fst := rfl

@[simp] theorem S1832BiconeOfCone_toB (s : PullbackCone (S1832Q f) (S1832Q g)) :
    (S1832BiconeOfCone s).toB = Quot.out s.snd := rfl

/-- The cone in the quotient category determined by a two-pullback datum: the
apex is the cover apex, the legs are the classes of the two projections. -/
noncomputable def S1832PullbackCone (P : S1832TwoPullback f g) :
    PullbackCone (S1832Q f) (S1832Q g) :=
  PullbackCone.mk (S1832Q P.toA) (S1832Q P.toB) (by
    have h : S1832Q (S1641CoverMapComp P.toA f) =
        S1832Q (S1641CoverMapComp P.toB g) :=
      Quot.sound ⟨by simpa only [S1641CoverMapComp_map] using P.commutes⟩
    calc S1832Q P.toA ≫ S1832Q f = S1832Q (S1641CoverMapComp P.toA f) :=
          S1832QuotComp P.toA f
      _ = S1832Q (S1641CoverMapComp P.toB g) := h
      _ = S1832Q P.toB ≫ S1832Q g := (S1832QuotComp P.toB g).symm)

/-- The lifting morphism of a cone, as the class of the bicategorical lift. -/
noncomputable def S1832LiftOfCone (P : S1832TwoPullback f g)
    (s : PullbackCone (S1832Q f) (S1832Q g)) : s.pt ⟶ P.apex :=
  S1832Q (P.lift s.pt (S1832BiconeOfCone s))

/-- The first triangle of the lifting morphism. -/
theorem S1832LiftOfCone_fst (P : S1832TwoPullback f g)
    (s : PullbackCone (S1832Q f) (S1832Q g)) :
    S1832LiftOfCone P s ≫ S1832Q P.toA = s.fst := by
  have h : S1832Q (S1641CoverMapComp (P.lift s.pt (S1832BiconeOfCone s)) P.toA) =
      s.fst := by
    have h0 : S1728CoverMapRel
        (S1641CoverMapComp (P.lift s.pt (S1832BiconeOfCone s)) P.toA)
        (Quot.out s.fst) :=
      ⟨by
        simpa only [S1641CoverMapComp_map, S1832BiconeOfCone_toA] using
          P.liftToA s.pt (S1832BiconeOfCone s)⟩
    calc S1832Q (S1641CoverMapComp (P.lift s.pt (S1832BiconeOfCone s)) P.toA)
        = S1832Q (Quot.out s.fst) := Quot.sound h0
      _ = s.fst := S1832Q_out s.fst
  calc S1832LiftOfCone P s ≫ S1832Q P.toA
      = S1832Q (S1641CoverMapComp (P.lift s.pt (S1832BiconeOfCone s)) P.toA) :=
        S1832QuotComp (P.lift s.pt (S1832BiconeOfCone s)) P.toA
    _ = s.fst := h

/-- The second triangle of the lifting morphism. -/
theorem S1832LiftOfCone_snd (P : S1832TwoPullback f g)
    (s : PullbackCone (S1832Q f) (S1832Q g)) :
    S1832LiftOfCone P s ≫ S1832Q P.toB = s.snd := by
  have h : S1832Q (S1641CoverMapComp (P.lift s.pt (S1832BiconeOfCone s)) P.toB) =
      s.snd := by
    have h0 : S1728CoverMapRel
        (S1641CoverMapComp (P.lift s.pt (S1832BiconeOfCone s)) P.toB)
        (Quot.out s.snd) :=
      ⟨by
        simpa only [S1641CoverMapComp_map, S1832BiconeOfCone_toB] using
          P.liftToB s.pt (S1832BiconeOfCone s)⟩
    calc S1832Q (S1641CoverMapComp (P.lift s.pt (S1832BiconeOfCone s)) P.toB)
        = S1832Q (Quot.out s.snd) := Quot.sound h0
      _ = s.snd := S1832Q_out s.snd
  calc S1832LiftOfCone P s ≫ S1832Q P.toB
      = S1832Q (S1641CoverMapComp (P.lift s.pt (S1832BiconeOfCone s)) P.toB) :=
        S1832QuotComp (P.lift s.pt (S1832BiconeOfCone s)) P.toB
    _ = s.snd := h

/-- Uniqueness of the lifting morphism in the quotient category, from the
bicategorical uniqueness of the lift. -/
theorem S1832LiftOfCone_unique (P : S1832TwoPullback f g)
    (s : PullbackCone (S1832Q f) (S1832Q g)) (m : s.pt ⟶ P.apex)
    (h1 : m ≫ S1832Q P.toA = s.fst) (h2 : m ≫ S1832Q P.toB = s.snd) :
    m = S1832LiftOfCone P s := by
  have hh1 : S1832Q (Quot.out m) ≫ S1832Q P.toA = S1832Q (Quot.out s.fst) := by
    calc S1832Q (Quot.out m) ≫ S1832Q P.toA = m ≫ S1832Q P.toA := by rw [S1832Q_out m]
      _ = s.fst := h1
      _ = S1832Q (Quot.out s.fst) := (S1832Q_out s.fst).symm
  have hh2 : S1832Q (Quot.out m) ≫ S1832Q P.toB = S1832Q (Quot.out s.snd) := by
    calc S1832Q (Quot.out m) ≫ S1832Q P.toB = m ≫ S1832Q P.toB := by rw [S1832Q_out m]
      _ = s.snd := h2
      _ = S1832Q (Quot.out s.snd) := (S1832Q_out s.snd).symm
  obtain ⟨e⟩ := P.uniq s.pt (S1832BiconeOfCone s) (Quot.out m)
    (S1832IsoOfCompEq (Quot.out m) P.toA (Quot.out s.fst) hh1)
    (S1832IsoOfCompEq (Quot.out m) P.toB (Quot.out s.snd) hh2)
  calc m = S1832Q (Quot.out m) := (S1832Q_out m).symm
    _ = S1832Q (P.lift s.pt (S1832BiconeOfCone s)) := Quot.sound ⟨e⟩
    _ = S1832LiftOfCone P s := rfl

/-- **The quotient universal property.**  A bicategorical two-pullback datum for
a cospan of actual cover maps yields a genuine limit cone of that cospan in the
actual 2-isomorphism quotient category. -/
noncomputable def S1832PullbackConeIsLimit (P : S1832TwoPullback f g) :
    IsLimit (S1832PullbackCone P) :=
  PullbackCone.isLimitAux (S1832PullbackCone P)
    (fun s => S1832LiftOfCone P s)
    (fun s => S1832LiftOfCone_fst P s)
    (fun s => S1832LiftOfCone_snd P s)
    (fun s m h =>
      S1832LiftOfCone_unique P s m (h WalkingCospan.left) (h WalkingCospan.right))

/-- A bicategorical two-pullback datum produces a limit of the cospan. -/
theorem S1832HasLimit_of_twoPullback (P : S1832TwoPullback f g) :
    HasLimit (cospan (S1832Q f) (S1832Q g)) :=
  HasLimit.mk ⟨S1832PullbackCone P, S1832PullbackConeIsLimit P⟩

/-- A bicategorical two-pullback datum produces a pullback in the quotient
category, in the HasPullback form. -/
theorem S1832HasPullback_of_twoPullback (P : S1832TwoPullback f g) :
    HasPullback (S1832Q f) (S1832Q g) :=
  S1832HasLimit_of_twoPullback P

end Main

/-! ## 4. HasPullbacks from bicategorical fibre products -/

/-- The statement that every cospan of actual cover maps admits a bicategorical
fibre-product cover.  This is the exact geometric obligation isolated here. -/
def S1832FirstMissingPullback : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    Nonempty (S1832TwoPullback f g)

/-- Bicategorical fibre products of covers give all pullbacks of the actual
2-isomorphism quotient category.  This discharges the quotient universal-property
half of S1762's pullback obligation. -/
theorem S1832HasPullbacks_of_squares (h : S1832FirstMissingPullback) :
    @HasPullbacks S1728Cover S1728ActualCategory11 := by
  haveI : ∀ {X Y Z : S1728Cover} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g) :=
    fun {X Y Z} {f g} => by
      obtain ⟨P⟩ := h X Y Z (Quot.out f) (Quot.out g)
      have hP := S1832HasLimit_of_twoPullback (f := Quot.out f) (g := Quot.out g) P
      rwa [S1832Q_out f, S1832Q_out g] at hP
  exact hasPullbacks_of_hasLimit_cospan S1728Cover

/-- S1762's literal pullback obligation follows from the bicategorical
fibre-product statement. -/
theorem S1832PullbackObligationActual_of_squares (h : S1832FirstMissingPullback) :
    S1762PullbackObligationActual :=
  S1832HasPullbacks_of_squares h



/-! ## 5. Unconditional instances: cospans with an identity leg

The apex is the other cover; the two comparison 2-cells are the bicategory
unitors, which is exactly the identity API used by S1762 for the terminal
object.  -/

section Identity

/-- The cospan (f, identity) has a bicategorical two-pullback, with apex the
source of f. -/
theorem S1832TwoPullback_id_right {A C : S1728Cover} (f : S1728CoverMap A C) :
    Nonempty (S1832TwoPullback f (S1641CoverMapId C)) := by
  refine ⟨?_⟩
  exact
    { apex := A
      toA := S1641CoverMapId A
      toB := f
      commutes := (S1728LeftUnitorIso f).trans (S1728RightUnitorIso f).symm
      lift := fun _ c => c.toA
      liftToA := fun _ c => S1728RightUnitorIso c.toA
      liftToB := fun _ c => c.commutes.trans (S1728RightUnitorIso c.toB)
      uniq := fun _ _ _ h1 _ => by
        obtain ⟨e⟩ := h1
        exact ⟨(S1728RightUnitorIso _).symm.trans e⟩ }

/-- The cospan (identity, g) has a bicategorical two-pullback, with apex the
source of g. -/
theorem S1832TwoPullback_id_left {B C : S1728Cover} (g : S1728CoverMap B C) :
    Nonempty (S1832TwoPullback (S1641CoverMapId C) g) := by
  refine ⟨?_⟩
  exact
    { apex := B
      toA := g
      toB := S1641CoverMapId B
      commutes := (S1728RightUnitorIso g).trans (S1728LeftUnitorIso g).symm
      lift := fun _ c => c.toB
      liftToA := fun _ c => c.commutes.symm.trans (S1728RightUnitorIso c.toA)
      liftToB := fun _ c => S1728RightUnitorIso c.toB
      uniq := fun _ _ _ _ h2 => by
        obtain ⟨e⟩ := h2
        exact ⟨(S1728RightUnitorIso _).symm.trans e⟩ }

/-- The cospan (f, identity) has an actual pullback in the quotient category. -/
theorem S1832HasPullback_id_right {A C : S1728Cover} (f : S1728CoverMap A C) :
    HasPullback (S1832Q f) (S1832Q (S1641CoverMapId C)) :=
  S1832HasPullback_of_twoPullback (Classical.choice (S1832TwoPullback_id_right f))

/-- The cospan (identity, g) has an actual pullback in the quotient category. -/
theorem S1832HasPullback_id_left {B C : S1728Cover} (g : S1728CoverMap B C) :
    HasPullback (S1832Q (S1641CoverMapId C)) (S1832Q g) :=
  S1832HasPullback_of_twoPullback (Classical.choice (S1832TwoPullback_id_left g))

end Identity

/-! ## 6. The converse: a pullback in the quotient category gives the
bicategorical datum -/

section Converse

variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}

/-- The cone in the quotient category attached to a pseudo-cone. -/
noncomputable def S1832BiconeToCone {W : S1728Cover} (c : S1832Bicone f g W) :
    PullbackCone (S1832Q f) (S1832Q g) :=
  PullbackCone.mk (S1832Q c.toA) (S1832Q c.toB) (by
    have h : S1832Q (S1641CoverMapComp c.toA f) =
        S1832Q (S1641CoverMapComp c.toB g) :=
      Quot.sound ⟨by simpa only [S1641CoverMapComp_map] using c.commutes⟩
    calc S1832Q c.toA ≫ S1832Q f = S1832Q (S1641CoverMapComp c.toA f) :=
          S1832QuotComp c.toA f
      _ = S1832Q (S1641CoverMapComp c.toB g) := h
      _ = S1832Q c.toB ≫ S1832Q g := (S1832QuotComp c.toB g).symm)

/-- **The converse.**  An actual pullback in the quotient category produces the
bicategorical two-pullback datum: the apex is the pullback object, the two
projections are chosen representatives of its legs, and the comparison
2-isomorphisms come from the equalities in the quotient. -/
noncomputable def S1832TwoPullbackOfHasPullback
    (H : HasPullback (S1832Q f) (S1832Q g)) : S1832TwoPullback f g := by
  letI : HasPullback (S1832Q f) (S1832Q g) := H
  let t : PullbackCone (S1832Q f) (S1832Q g) := pullback.cone (S1832Q f) (S1832Q g)
  have ht : IsLimit t := pullback.isLimit (S1832Q f) (S1832Q g)
  refine
    { apex := t.pt
      toA := Quot.out t.fst
      toB := Quot.out t.snd
      commutes := S1832ConeCommutesOfEq t.fst t.snd t.condition
      lift := fun _ c => Quot.out (ht.lift (S1832BiconeToCone c))
      liftToA := fun _ c => ?_
      liftToB := fun _ c => ?_
      uniq := fun _ c h h1 h2 => ?_ }
  · have hclass : S1832Q (S1641CoverMapComp
        (Quot.out (ht.lift (S1832BiconeToCone c))) (Quot.out t.fst)) =
        S1832Q c.toA := by
      rw [← S1832QuotComp]
      calc S1832Q (Quot.out (ht.lift (S1832BiconeToCone c))) ≫ S1832Q (Quot.out t.fst)
          = ht.lift (S1832BiconeToCone c) ≫ t.fst := by
            rw [S1832Q_out (ht.lift (S1832BiconeToCone c)), S1832Q_out t.fst]
        _ = (S1832BiconeToCone c).fst := ht.fac (S1832BiconeToCone c) WalkingCospan.left
        _ = S1832Q c.toA := rfl
    exact Classical.choice
      (S1832IsoOfCompEq (Quot.out (ht.lift (S1832BiconeToCone c))) (Quot.out t.fst)
        c.toA hclass)
  · have hclass : S1832Q (S1641CoverMapComp
        (Quot.out (ht.lift (S1832BiconeToCone c))) (Quot.out t.snd)) =
        S1832Q c.toB := by
      rw [← S1832QuotComp]
      calc S1832Q (Quot.out (ht.lift (S1832BiconeToCone c))) ≫ S1832Q (Quot.out t.snd)
          = ht.lift (S1832BiconeToCone c) ≫ t.snd := by
            rw [S1832Q_out (ht.lift (S1832BiconeToCone c)), S1832Q_out t.snd]
        _ = (S1832BiconeToCone c).snd := ht.fac (S1832BiconeToCone c) WalkingCospan.right
        _ = S1832Q c.toB := rfl
    exact Classical.choice
      (S1832IsoOfCompEq (Quot.out (ht.lift (S1832BiconeToCone c))) (Quot.out t.snd)
        c.toB hclass)
  · have hm1 : S1832Q h ≫ t.fst = (S1832BiconeToCone c).fst := by
      have hrel : S1728CoverMapRel (S1641CoverMapComp h (Quot.out t.fst)) c.toA :=
        ⟨by simpa only [S1641CoverMapComp_map] using Classical.choice h1⟩
      calc S1832Q h ≫ t.fst = S1832Q (S1641CoverMapComp h (Quot.out t.fst)) :=
            S1832QuotCompMk' h (Quot.out t.fst) (S1832Q_out t.fst).symm
        _ = S1832Q c.toA := Quot.sound hrel
        _ = (S1832BiconeToCone c).fst := rfl
    have hm2 : S1832Q h ≫ t.snd = (S1832BiconeToCone c).snd := by
      have hrel : S1728CoverMapRel (S1641CoverMapComp h (Quot.out t.snd)) c.toB :=
        ⟨by simpa only [S1641CoverMapComp_map] using Classical.choice h2⟩
      calc S1832Q h ≫ t.snd = S1832Q (S1641CoverMapComp h (Quot.out t.snd)) :=
            S1832QuotCompMk' h (Quot.out t.snd) (S1832Q_out t.snd).symm
        _ = S1832Q c.toB := Quot.sound hrel
        _ = (S1832BiconeToCone c).snd := rfl
    have huniq : S1832Q h = ht.lift (S1832BiconeToCone c) :=
      PullbackCone.IsLimit.hom_ext ht
        (by
          rw [hm1]
          exact (ht.fac (S1832BiconeToCone c) WalkingCospan.left).symm)
        (by
          rw [hm2]
          exact (ht.fac (S1832BiconeToCone c) WalkingCospan.right).symm)
    have hEq : S1832Q h = S1832Q (Quot.out (ht.lift (S1832BiconeToCone c))) := by
      rw [S1832Q_out (ht.lift (S1832BiconeToCone c))]
      exact huniq
    exact S1832RelOfQuotEq hEq

/-- **The exact obligation, identified.**  HasPullbacks of the actual
2-isomorphism quotient category is equivalent to the existence of a bicategorical
fibre-product cover for every cospan of actual cover maps. -/
theorem S1832FirstMissing_iff_hasPullbacks :
    S1832FirstMissingPullback ↔ @HasPullbacks S1728Cover S1728ActualCategory11 :=
  ⟨S1832HasPullbacks_of_squares, fun H => by
    intro A B C f g
    haveI : @HasPullbacks S1728Cover S1728ActualCategory11 := H
    exact ⟨S1832TwoPullbackOfHasPullback (f := f) (g := g) inferInstance⟩⟩

/-- The exact obligation in S1762's literal form. -/
theorem S1832FirstMissing_iff_S1762 :
    S1832FirstMissingPullback ↔ S1762PullbackObligationActual :=
  S1832FirstMissing_iff_hasPullbacks

end Converse

/-! ## 7. Consumers: the finite-limit and PreGalois fields -/

/-- The bicategorical fibre-product statement feeds S1762's finite-limit field
(whose terminal input is already closed by S1762). -/
theorem S1832HasFiniteLimitsActual (h : S1832FirstMissingPullback) :
    S1736ObligationFiniteLimits (F := S1762K) (X := S1762X) :=
  S1762HasFiniteLimits_of_pullbacks (S1832PullbackObligationActual_of_squares h)

/-- The bicategorical fibre-product statement completes the four remaining
PreGalois inputs of S1762 into the actual PreGaloisCategory. -/
theorem S1832PreGaloisCategoryOfSquares (h : S1832FirstMissingPullback)
    (hCoprod : S1762FiniteCoproductObligationActual)
    (hQuot : S1762FiniteGroupQuotientObligationActual)
    (hMono : S1762MonoDirectSummandObligationActual) :
    S1736ActualPreGaloisObligation (F := S1762K) (X := S1762X) :=
  S1762PreGaloisCategoryOfRemainingInputs (S1832PullbackObligationActual_of_squares h)
    hCoprod hQuot hMono

/-! ## 8. Checks and axiom audit -/

#check S1832Q
#check S1832RelOfQuotEq
#check S1832QuotComp
#check S1832Bicone
#check S1832TwoPullback
#check S1832BiconeOfCone
#check S1832PullbackCone
#check S1832LiftOfCone
#check S1832PullbackConeIsLimit
#check S1832HasLimit_of_twoPullback
#check S1832HasPullback_of_twoPullback
#check S1832FirstMissingPullback
#check S1832HasPullbacks_of_squares
#check S1832PullbackObligationActual_of_squares
#check S1832TwoPullback_id_right
#check S1832TwoPullback_id_left
#check S1832HasPullback_id_right
#check S1832HasPullback_id_left
#check S1832BiconeToCone
#check S1832TwoPullbackOfHasPullback
#check S1832FirstMissing_iff_hasPullbacks
#check S1832FirstMissing_iff_S1762
#check S1832HasFiniteLimitsActual
#check S1832PreGaloisCategoryOfSquares

#print axioms S1832RelOfQuotEq
#print axioms S1832QuotComp
#print axioms S1832ConeCommutesOfEq
#print axioms S1832IsoOfCompEq
#print axioms S1832PullbackCone
#print axioms S1832LiftOfCone
#print axioms S1832PullbackConeIsLimit
#print axioms S1832HasPullbacks_of_squares
#print axioms S1832PullbackObligationActual_of_squares
#print axioms S1832TwoPullback_id_right
#print axioms S1832TwoPullback_id_left
#print axioms S1832HasPullback_id_right
#print axioms S1832HasPullback_id_left
#print axioms S1832TwoPullbackOfHasPullback
#print axioms S1832FirstMissing_iff_hasPullbacks
#print axioms S1832FirstMissing_iff_S1762
#print axioms S1832HasFiniteLimitsActual
#print axioms S1832PreGaloisCategoryOfSquares

end LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual