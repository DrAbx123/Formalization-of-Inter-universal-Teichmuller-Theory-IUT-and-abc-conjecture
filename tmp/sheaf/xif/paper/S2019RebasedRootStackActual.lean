import tmp.sheaf.xif.paper.S2015FullPullbackActual
import tmp.sheaf.xif.paper.S2013RootHomSheafActual

/-!
# S2019: the root stackification rebased on the corrected full property

## The problem

S1997 recorded the remaining K-side input for the `l`-tors root stack at the origin
as the structure

  `S1997RootStackification K l = { stack, isStack, comparison, origin_faithful }`

(an etale stack `Q`, a comparison `e : S1997RootPrestack K l -> Q` faithful at the
origin).  S2002/S2008/S2013 split the stack condition for the root prestack into
`IsPrestack` (proved unconditionally in S2013) and the effective-descent statement
`S1997RootEffectiveDescent K l`.

Two independent weaknesses of the *recorded* interface must be separated:

* the recorded base-change presentation `EtaleStackBaseChangePresentation` stores
  only the weak seven-field `TwoPullbackWitness`; S2010 refuted, for that
  definition, the target "the recorded square is the actual pullback", and S2015
  repaired it by the corrected full 2-universal property / actual iso-comma
  presentation `S2015FullPullback` and `S2015FullBaseChangePresentation`;

* `Pseudofunctor.IsStack` itself asks only for `IsPrestack` plus essential
  surjectivity of `toDescentData`.  This file proves that for a *prestack* this
  weak-looking condition is already the full 2-dimensional (actual iso-comma)
  condition: the descent functor is fully faithful, so essential surjectivity is
  existence plus uniqueness up to isomorphism of lifts.  Rebasing `IsStack` on the
  corrected full 2-universal property is therefore *conservative*.

## What is defined

1. `S2019IsoCommaDescent F R` (section 1): the corrected full descent datum of a
   category-valued pseudofunctor `F` at a sieve `R`, in the actual iso-comma form
   of `S2015FullPullback`: every descent datum admits a lift (`exists_lift`) and any
   two lifts of the same descent datum are isomorphic (`unique_lift`).  This is the
   descent-data analogue of S2015's two fields.

2. `S2019FullIsStack F` (section 1): `F` is a prestack and satisfies the corrected
   full descent datum at every covering sieve.  This is the root-stackification stack
   condition *rebased* on S2015's corrected full 2-universal property.

3. `S2019RootFullDescentAll` / `S2019RootFullIsStack` / `S2019FirstMissing`
   (section 2): the correction specialised to `S1997RootPrestack K l`, and the named
   first missing after the rebasing.

4. `S2019CorrectedIdentityPresentation` / `S2019CorrectedFiniteEtale` /
   `S2019CorrectedFiniteEtaleAll` (section 3): S2015's corrected base-change data for
   the covers of S1728 -- the base-change presentations the recorded weak witnesses
   cannot supply.

5. `S2019CorrectedRootStackDatum K l` (section 4): **the corrected root stack datum**,
   S1997's root stackification with the weak `isStack` field replaced by the corrected
   full descent condition `S2019FullIsStack`, the comparison and origin faithfulness
   unchanged.

6. `S2019RebasedRootStackRoute l` (section 5): the rebased route with its two inputs
   made explicit (their logical independence is not claimed here).

## What is proved

General (any site, any category-valued pseudofunctor):

* `S2019IsoCommaDescent_iff_essSurj`: for a prestack, the corrected full descent
  datum at a covering sieve is equivalent to essential surjectivity of the descent
  functor, i.e. to the recorded effective-descent condition.

* `S2019FullIsStack_iff_IsStack`: the corrected full stack condition is equivalent
  to Mathlib's `IsStack` (through S2002's
  `isStack_of_isPrestack_and_essSurj` and Mathlib's
  `Pseudofunctor.IsStack.essSurj_of_sieve`).  Hence the recorded `IsStack` is not
  weak in the way `TwoPullbackWitness` is.

Root prestack:

* `S2019RootIsStack_iff_fullDescentAll`: `IsStack` for the root prestack is exactly
  the corrected full descent datum at every covering sieve.

* `S2019RootFullDescentAll_iff_effDescent`: the corrected full descent statement is
  exactly S1997's recorded `S1997RootEffectiveDescent`.  This is the central audit
  finding: the S2015 repair changes nothing at the effective-descent level, so the
  Kummer non-effectivity recalled in S2002 (expected failure of
  `S1997RootEffectiveDescent`) is a genuine mathematical obstruction and not an
  artefact of a weak formulation.

Covers:

* `S2019CorrectedFiniteEtaleAll_uniq` / `S2019UniqFirstMissing_of_identityPresentations`:
  the corrected S2015 data implies `S2001UniqFirstMissing`.

* `S2019CorrectedFull_iff_missingHalf`: for a fixed recorded weak witness, the
  corrected full property is exactly the missing essential-surjectivity half
  (`S1827EssSurjOf`), so the rebasing adds exactly the half S1827/S1841 isolated.

* `S2019_noSchemaFromWitness`, `S2019_counterexample_identity_not_corrected`,
  `S2019_recorded_full_refuted`: the recorded weak witnesses do not produce the
  corrected presentations (S2015/S2010).  The corrected presentations are therefore
  data, not a property of the recorded witnesses.

Corrected root stack datum:

* `S2019CorrectedRootStackMissing_iff`: the corrected root stack datum is inhabited
  iff S1997's recorded root stackification is.  The rebasing is exact (no weakening,
  no extra assumption); `toRecorded` and `ofRecorded` are the two directions.

* `S2019CorrectedRootStackMissing_implies_S1994`: a corrected root stack datum over
  `A.K` yields S1994's stacky orbicurve `S1994StackyOrbicurveMissing l A`;
  `S2019CorrectedRootStack_witness_aut` and
  `S2019CorrectedRootStack_not_discreteFiber` transport the order-`l` origin
  automorphism and the non-discreteness of the fibres.

* `S2019RebasedRootStackRoute_iff`: the rebased route is exactly the recorded root
  stackification together with S2015's corrected finite-etale data;
  `S2019RebasedRootStackRoute_uniq` shows the route delivers
  `S2001UniqFirstMissing`.

## Exact first missing after the rebasing

`S2019FirstMissing K l` (section 2) is the corrected full (actual iso-comma)
descent datum of the root prestack at every covering sieve.  It is *equivalent* to
S1997's recorded effective descent and to `IsStack`, and it is **not proved here**.
S2002/S2010 indicate that `S1997RootEffectiveDescent` is expected to fail for Kummer
covers (the twisted datum `b = 0` with the nontrivial `mu_l`-cocycle has no effective
realisation in the prestack), and this file does not attempt to prove it.  What the
rebasing on S2015 establishes is that this obstruction is intrinsic: the recorded
stack condition already is the full 2-universal (actual iso-comma) condition, so no
strengthening of the stack condition can remove it.  The only input that S2015's
repair genuinely strengthens is the base-change presentation data of the covers,
where the weak `TwoPullbackWitness` fails (S2010).

## Honest boundary

No `sorry`, no new axiom, no `Shrink`/`ULift`/`PUnit`, no fabricated stack,
equivalence, 2-cell or `IsStack` instance.  The corrected structures are definitions;
the theorems are proved from them and from the existing tree (S1994, S1997, S2002,
S2007, S2010, S2013, S2015).  `S2019FirstMissing` and `S2015CorrectedRepair` are
named statements with no inhabitant asserted.  The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2019RebasedRootStackActual

open CategoryTheory Opposite
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1994KSideCovers
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual
open LeanFormal.IUT.XiFPaper.S2002RootStackificationActual
open LeanFormal.IUT.XiFPaper.S2007CoverFiberDiscreteActual
open LeanFormal.IUT.XiFPaper.S2010BaseChangeFullActual
open LeanFormal.IUT.XiFPaper.S2013RootHomSheafActual
open LeanFormal.IUT.XiFPaper.S2015FullPullbackActual

universe u

/-! ## 1. The corrected full descent property (actual iso-comma) -/

section GeneralDescent

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}

/-- The descent functor of a category-valued pseudofunctor at a sieve. -/
abbrev S2019DtDFunctor (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat) {S : C} (R : Sieve S) :
    F.obj (LocallyDiscrete.mk (op S)) ⥤
      F.DescentData (fun i : R.arrows.category => i.obj.hom) :=
  F.toDescentData (fun i : R.arrows.category => i.obj.hom)

/-- The corrected full descent datum of `F` at a sieve `R`, in the actual iso-comma
form of S2015's `S2015FullPullback`: every descent datum admits a lift and any two
lifts of the same descent datum are isomorphic.  This is the descent-data analogue
of the corrected full 2-universal property. -/
structure S2019IsoCommaDescent (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat) {S : C}
    (R : Sieve S) : Prop where
  /-- Every descent datum over `R` is realised by an object over `S`. -/
  exists_lift : ∀ d : F.DescentData (fun i : R.arrows.category => i.obj.hom),
    ∃ x : F.obj (LocallyDiscrete.mk (op S)),
      Nonempty (d ≅ (S2019DtDFunctor F R).obj x)
  /-- Uniqueness, up to isomorphism, of the realisation of a descent datum. -/
  unique_lift : ∀ (d : F.DescentData (fun i : R.arrows.category => i.obj.hom))
    (x y : F.obj (LocallyDiscrete.mk (op S))),
    Nonempty (d ≅ (S2019DtDFunctor F R).obj x) →
    Nonempty (d ≅ (S2019DtDFunctor F R).obj y) →
      Nonempty (x ≅ y)

/-- For a prestack, the corrected full descent datum is exactly essential
surjectivity of the descent functor, i.e. the recorded effective-descent condition.
The uniqueness half is a consequence of full faithfulness of the descent functor,
which is what `IsPrestack` provides. -/
theorem S2019IsoCommaDescent_iff_essSurj (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    [F.IsPrestack J] {S : C} {R : Sieve S} (hR : R ∈ J S) :
    S2019IsoCommaDescent F R ↔ (S2019DtDFunctor F R).EssSurj := by
  constructor
  · intro h
    refine ⟨fun d => ?_⟩
    obtain ⟨x, ⟨e⟩⟩ := h.exists_lift d
    exact ⟨x, ⟨e.symm⟩⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro d
      haveI := h
      exact ⟨(S2019DtDFunctor F R).objPreimage d,
        ⟨((S2019DtDFunctor F R).objObjPreimageIso d).symm⟩⟩
    · intro d x y hx hy
      obtain ⟨ex⟩ := hx
      obtain ⟨ey⟩ := hy
      have hff := (F.isPrestackFor' R hR).fullyFaithful
      exact ⟨hff.isoEquiv.symm (ex.symm.trans ey)⟩

/-- The corrected full stack condition: `F` is a prestack and satisfies the corrected
full descent datum at every covering sieve.  This is the stack condition rebased on
S2015's corrected full 2-universal property. -/
def S2019FullIsStack (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat) : Prop :=
  F.IsPrestack J ∧ ∀ (S : C) (R : Sieve S), R ∈ J S → S2019IsoCommaDescent F R

/-- The corrected full stack condition is equivalent to Mathlib's `IsStack`: the
rebasing of stackhood on the corrected full 2-universal property is conservative. -/
theorem S2019FullIsStack_iff_IsStack (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat) :
    S2019FullIsStack (J := J) F ↔ F.IsStack J := by
  constructor
  · rintro ⟨hpre, hfull⟩
    exact isStack_of_isPrestack_and_essSurj F hpre
      (fun S R hR => (S2019IsoCommaDescent_iff_essSurj F hR).mp (hfull S R hR))
  · intro h
    haveI := h
    refine ⟨h.toIsPrestack, fun S R hR => (S2019IsoCommaDescent_iff_essSurj F hR).mpr ?_⟩
    exact Pseudofunctor.IsStack.essSurj_of_sieve F R hR

end GeneralDescent

/-! ## 2. The root prestack rebased on the corrected full descent -/

section RootPrestack

variable {K : Type u} [Field K] {l : PrimeGeFive}

/-- The corrected full (actual iso-comma) descent datum of the root prestack at every
covering sieve of the etale topology. -/
def S2019RootFullDescentAll : Prop :=
  ∀ (S : SchemeOverField K) (R : Sieve S), R ∈ SchemeOverField.etaleTopology K S →
    S2019IsoCommaDescent (S1997RootPrestack K l.value) R

/-- The corrected full stack condition for the root prestack. -/
def S2019RootFullIsStack : Prop :=
  S2019FullIsStack (J := SchemeOverField.etaleTopology K) (S1997RootPrestack K l.value)

/-- The corrected full stack condition for the root prestack is its corrected full
descent datum at every covering sieve; the prestack half is S2013's unconditional
`S2013RootPrestack_isPrestack`. -/
theorem S2019RootFullIsStack_iff_fullDescentAll :
    S2019RootFullIsStack (K := K) (l := l) ↔ S2019RootFullDescentAll (K := K) (l := l) := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨S2013RootPrestack_isPrestack (K := K) (l := l), h⟩

/-- `IsStack` for the root prestack is exactly the corrected full descent datum at
every covering sieve. -/
theorem S2019RootIsStack_iff_fullDescentAll :
    (S1997RootPrestack K l.value).IsStack (SchemeOverField.etaleTopology K) ↔
      S2019RootFullDescentAll (K := K) (l := l) :=
  (S2019FullIsStack_iff_IsStack (J := SchemeOverField.etaleTopology K)
    (S1997RootPrestack K l.value)).symm.trans
    (S2019RootFullIsStack_iff_fullDescentAll (K := K) (l := l))

/-- The recorded effective descent of the root prestack is exactly the corrected full
descent datum: the rebasing on S2015 changes nothing at this level. -/
theorem S2019RootFullDescentAll_iff_effDescent :
    S2019RootFullDescentAll (K := K) (l := l) ↔ S1997RootEffectiveDescent K l.value :=
  (S2019RootIsStack_iff_fullDescentAll (K := K) (l := l)).symm.trans
    (S2013isStack_iff (K := K) (l := l))

/-- **The exact first missing after the rebasing**, in corrected (actual iso-comma)
full descent form.  It is not proved here; it is equivalent to S1997's recorded
effective descent and to `IsStack` for the root prestack. -/
def S2019FirstMissing : Prop := S2019RootFullDescentAll (K := K) (l := l)

/-- The corrected first missing is the stack condition of the root prestack. -/
theorem S2019FirstMissing_iff_IsStack :
    S2019FirstMissing (K := K) (l := l) ↔
      (S1997RootPrestack K l.value).IsStack (SchemeOverField.etaleTopology K) :=
  (S2019RootFullDescentAll_iff_effDescent (K := K) (l := l)).trans
    (S2013isStack_iff (K := K) (l := l)).symm

/-- The corrected first missing is exactly S1997's recorded effective descent. -/
theorem S2019FirstMissing_iff_effDescent :
    S2019FirstMissing (K := K) (l := l) ↔ S1997RootEffectiveDescent K l.value :=
  S2019RootFullDescentAll_iff_effDescent (K := K) (l := l)

/-- The corrected full descent datum supplies the recorded effective descent. -/
theorem S2019RootFullDescentAll_effDescent
    (h : S2019RootFullDescentAll (K := K) (l := l)) : S1997RootEffectiveDescent K l.value :=
  (S2019RootFullDescentAll_iff_effDescent (K := K) (l := l)).mp h

/-- The recorded effective descent supplies the corrected full descent datum. -/
theorem S2019RootFullDescentAll_of_effDescent
    (h : S1997RootEffectiveDescent K l.value) : S2019RootFullDescentAll (K := K) (l := l) :=
  (S2019RootFullDescentAll_iff_effDescent (K := K) (l := l)).mpr h

/-- The corrected full descent datum yields `IsStack` for the root prestack. -/
theorem S2019RootIsStack_of_fullDescentAll
    (h : S2019RootFullDescentAll (K := K) (l := l)) :
    (S1997RootPrestack K l.value).IsStack (SchemeOverField.etaleTopology K) :=
  (S2019RootIsStack_iff_fullDescentAll (K := K) (l := l)).mpr h

end RootPrestack

/-! ## 3. The corrected base-change presentations of the covers (S2015) -/

section CorrectedCover

/-- The corrected identity-point base-change presentation of a cover: S2015's actual
iso-comma presentation (weak witness *and* corrected full 2-universal property). -/
abbrev S2019CorrectedIdentityPresentation (C : S1728Cover) : Type 1 :=
  S2015FullBaseChangePresentation C.map S1726AffineOver S1733BasePoint

/-- The corrected identity-point presentation, as a proposition. -/
def S2019CorrectedIdentityPresentationData (C : S1728Cover) : Prop :=
  Nonempty (S2019CorrectedIdentityPresentation C)

/-- The corrected finite-etale structure of a cover: actual iso-comma base-change
presentations at every scheme-valued point (S2015). -/
def S2019CorrectedFiniteEtale (C : S1728Cover) : Prop :=
  Nonempty (S2015FullFiniteEtale C.map)

/-- The corrected finite-etale data of all covers, uniformly. -/
def S2019CorrectedFiniteEtaleAll : Prop := ∀ C : S1728Cover, S2019CorrectedFiniteEtale C

/-- The corrected finite-etale data of all covers is literally S2015's
`S2015CorrectedRepair`. -/
theorem S2019CorrectedFiniteEtaleAll_iff : S2019CorrectedFiniteEtaleAll ↔ S2015CorrectedRepair :=
  Iff.rfl

/-- The corrected finite-etale data of all covers implies the corrected
identity-point presentations of all covers. -/
theorem S2019CorrectedIdentityPresentationAll_of_finiteEtaleAll
    (h : S2019CorrectedFiniteEtaleAll) :
    ∀ C : S1728Cover, S2019CorrectedIdentityPresentationData C :=
  S2015IdentityRepairAll_of_correctedRepair h

/-- The corrected identity-point presentations give S2001's cover-fibre
discreteness. -/
theorem S2019UniqFirstMissing_of_identityPresentations
    (h : ∀ C : S1728Cover, S2019CorrectedIdentityPresentationData C) :
    S2001UniqFirstMissing :=
  S2015UniqFirstMissing_of_identityRepairAll h

/-- The corrected finite-etale data gives S2001's cover-fibre discreteness. -/
theorem S2019CorrectedFiniteEtaleAll_uniq
    (h : S2019CorrectedFiniteEtaleAll) : S2001UniqFirstMissing :=
  S2015UniqFirstMissing_of_correctedRepair h

/-- The corrected identity-point presentation is, in particular, the recorded
base-change presentation: the corrected datum refines the recorded one. -/
noncomputable def S2019CorrectedIdentityPresentation_toRecorded (C : S1728Cover)
    (P : S2019CorrectedIdentityPresentation C) :
    EtaleStackBaseChangePresentation C.map S1726AffineOver S1733BasePoint :=
  S2015FullBaseChangePresentation.toRecorded P

/-- For a fixed recorded weak witness, the corrected full property of the square is
exactly the missing essential-surjectivity half: the rebasing adds exactly the half
S1827/S1841 isolated. -/
theorem S2019CorrectedFull_iff_missingHalf {P X Y Z : EtaleStackPseudofunctor S1726K}
    {sq : EtalePseudofunctorSquare P X Y Z} (w : sq.TwoPullbackWitness) :
    S2015FullPullback sq ↔ S1827EssSurjOf sq w :=
  S2015FullPullback_iff_essSurj w

/-- The corrected finite-etale structure gives the recorded finite-etale structure. -/
theorem S2019CorrectedFiniteEtale_toRecorded (C : S1728Cover)
    (h : S2019CorrectedFiniteEtale C) :
    Nonempty (EtaleStackFiniteEtaleMorphism C.map) := by
  obtain ⟨fe⟩ := h
  exact ⟨fe.toRecorded⟩

/-- The recorded weak witnesses do not produce the corrected full property uniformly
(S2015/S2010). -/
theorem S2019_noSchemaFromWitness :
    ¬ (∀ (P X Y Z : EtaleStackPseudofunctor S1726K)
        (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness),
        S2015FullPullback sq) :=
  S2015_not_fullOfWitness

/-- The recorded identity-point square of S2010's counterexample cover is not the
actual iso-comma fibre: the corrected data cannot be obtained by keeping the recorded
apex. -/
theorem S2019_counterexample_identity_not_corrected :
    ¬ S2015FullPullback (S1743Square S2010CounterCover) :=
  S2015_not_full_counterexample

/-- The uniform statement that the recorded weak presentations are already the actual
iso-comma fibre is false: the corrected presentations are data. -/
theorem S2019_recorded_full_refuted : ¬ S2015RecordedFullAll :=
  S2015_not_recordedFullAll

end CorrectedCover

/-! ## 4. The corrected root stack datum -/

section CorrectedRootStack

variable {K : Type u} [Field K] {l : PrimeGeFive}

/-- **The corrected root stack datum.**  S1997's root stackification with the weak
`IsStack` field replaced by the corrected full descent condition
`S2019FullIsStack` (the actual iso-comma full 2-universal property at every covering
sieve); the stack, the comparison from the root prestack and the faithfulness at the
origin are unchanged. -/
structure S2019CorrectedRootStackDatum (K : Type u) [Field K] (l : PrimeGeFive) where
  /-- The etale stack receiving the root prestack. -/
  stack : EtaleStackPseudofunctor K
  /-- The corrected full stack condition (actual iso-comma full descent). -/
  fullStack : S2019FullIsStack (J := SchemeOverField.etaleTopology K) stack
  /-- The comparison from the root prestack. -/
  comparison : Pseudofunctor.StrongTrans (S1997RootPrestack K l.value) stack
  /-- Faithfulness of the comparison at the origin. -/
  origin_faithful : S2002FaithfulAtOrigin stack comparison

/-- Forgetting the corrected stack condition gives S1997's recorded root
stackification. -/
noncomputable def S2019CorrectedRootStackDatum.toRecorded
    (D : S2019CorrectedRootStackDatum K l) : S1997RootStackification K l where
  stack := D.stack
  isStack := (S2019FullIsStack_iff_IsStack (J := SchemeOverField.etaleTopology K)
    D.stack).mp D.fullStack
  comparison := D.comparison
  origin_faithful := fun f hf => D.origin_faithful f hf

/-- Upgrading S1997's recorded root stackification gives the corrected datum. -/
noncomputable def S2019CorrectedRootStackDatum.ofRecorded
    (W : S1997RootStackification K l) : S2019CorrectedRootStackDatum K l where
  stack := W.stack
  fullStack := (S2019FullIsStack_iff_IsStack (J := SchemeOverField.etaleTopology K)
    W.stack).mpr W.isStack
  comparison := W.comparison
  origin_faithful := fun f hf => W.origin_faithful f hf

/-- The corrected root stack datum is inhabited iff S1997's recorded root
stackification is: the rebasing is exact. -/
theorem S2019CorrectedRootStackMissing_iff :
    Nonempty (S2019CorrectedRootStackDatum K l) ↔ S1997RootStackificationMissing K l :=
  ⟨fun h => h.elim fun D => ⟨D.toRecorded⟩,
    fun h => h.elim fun W => ⟨S2019CorrectedRootStackDatum.ofRecorded W⟩⟩

/-- The corrected root stack datum supplies S1997's recorded root stackification. -/
theorem S2019CorrectedRootStack_supplies_recorded
    (D : S2019CorrectedRootStackDatum K l) : S1997RootStackificationMissing K l :=
  ⟨D.toRecorded⟩

/-- Conversely the recorded root stackification supplies the corrected datum. -/
theorem S2019CorrectedRootStack_of_recorded
    (W : S1997RootStackification K l) : Nonempty (S2019CorrectedRootStackDatum K l) :=
  ⟨S2019CorrectedRootStackDatum.ofRecorded W⟩

/-- Any corrected root stack datum carries the order-`l` automorphism of the origin to a
nontrivial order-`l` automorphism of the image point. -/
theorem S2019CorrectedRootStack_witness_aut (D : S2019CorrectedRootStackDatum K l) :
    S2002WitnessAut D.toRecorded ^ l.value = 1 ∧
      S2002WitnessAut D.toRecorded ≠ 𝟙 (S2002WitnessImage D.toRecorded) :=
  S2002_witness_aut D.toRecorded

/-- The stack of any corrected root stack datum has non-discrete fibres: it is
genuinely stacky. -/
theorem S2019CorrectedRootStack_not_discreteFiber (D : S2019CorrectedRootStackDatum K l) :
    ¬ S2002DiscreteFiber D.stack :=
  S2002_witness_not_discreteFiber D.toRecorded

/-- **Consumer.**  A corrected root stack datum over `A.K` yields S1994's stacky
orbicurve. -/
theorem S2019CorrectedRootStackMissing_implies_S1994 {l : PrimeGeFive}
    {A : InitialThetaArithmeticData l}
    (h : Nonempty (S2019CorrectedRootStackDatum A.K l)) :
    S1994StackyOrbicurveMissing l A :=
  S1997FirstMissing_implies_S1994Stacky
    ((S2019CorrectedRootStackMissing_iff (K := A.K) (l := l)).mp h)

end CorrectedRootStack

/-! ## 5. The rebased route and its exact first missing -/

section RebasedRoute

/-- The rebased root-stack route: a corrected root stack datum over `S1726K` together
with S2015's corrected finite-etale data for all covers.  These are the two inputs
that the rebasing makes explicit: the stack condition rebased on the actual iso-comma
full property (proved equivalent to the recorded one), and the base-change
presentations genuinely corrected (the recorded weak witnesses are refuted, S2010).
Their logical independence is not claimed here. -/
def S2019RebasedRootStackRoute (l : PrimeGeFive) : Prop :=
  Nonempty (S2019CorrectedRootStackDatum S1726K l) ∧ S2019CorrectedFiniteEtaleAll

/-- The rebased route is exactly the recorded root stackification together with
S2015's corrected finite-etale data. -/
theorem S2019RebasedRootStackRoute_iff (l : PrimeGeFive) :
    S2019RebasedRootStackRoute l ↔
      S1997RootStackificationMissing S1726K l ∧ S2019CorrectedFiniteEtaleAll :=
  and_congr (S2019CorrectedRootStackMissing_iff (K := S1726K) (l := l)) Iff.rfl

/-- The rebased route delivers the recorded root stackification. -/
theorem S2019RebasedRootStackRoute_supplies_recorded (l : PrimeGeFive)
    (h : S2019RebasedRootStackRoute l) : S1997RootStackificationMissing S1726K l :=
  ((S2019RebasedRootStackRoute_iff l).mp h).1

/-- The rebased route delivers S2001's cover-fibre discreteness. -/
theorem S2019RebasedRootStackRoute_uniq (l : PrimeGeFive)
    (h : S2019RebasedRootStackRoute l) : S2001UniqFirstMissing :=
  S2019CorrectedFiniteEtaleAll_uniq ((S2019RebasedRootStackRoute_iff l).mp h).2

/-- The rebased route delivers the corrected identity-point presentations of all
covers. -/
theorem S2019RebasedRootStackRoute_identityPresentations (l : PrimeGeFive)
    (h : S2019RebasedRootStackRoute l) :
    ∀ C : S1728Cover, S2019CorrectedIdentityPresentationData C :=
  S2019CorrectedIdentityPresentationAll_of_finiteEtaleAll
    ((S2019RebasedRootStackRoute_iff l).mp h).2

/-- The rebased route's root stack component has an order-`l` automorphism at the origin:
the stacky point survives the rebasing. -/
theorem S2019RebasedRootStackRoute_witness_aut (l : PrimeGeFive)
    (h : S2019RebasedRootStackRoute l) :
    ∃ D : S2019CorrectedRootStackDatum S1726K l,
      S2002WitnessAut D.toRecorded ^ l.value = 1 ∧
        S2002WitnessAut D.toRecorded ≠ 𝟙 (S2002WitnessImage D.toRecorded) := by
  obtain ⟨D⟩ := h.1
  exact ⟨D, S2019CorrectedRootStack_witness_aut D⟩

end RebasedRoute

/-! ## 6. Checks and axiom audit -/

#check S2019DtDFunctor
#check S2019IsoCommaDescent
#check S2019IsoCommaDescent_iff_essSurj
#check S2019FullIsStack
#check S2019FullIsStack_iff_IsStack
#check S2019RootFullDescentAll
#check S2019RootFullIsStack
#check S2019RootFullIsStack_iff_fullDescentAll
#check S2019RootIsStack_iff_fullDescentAll
#check S2019RootFullDescentAll_iff_effDescent
#check S2019FirstMissing
#check S2019FirstMissing_iff_IsStack
#check S2019FirstMissing_iff_effDescent
#check S2019RootFullDescentAll_effDescent
#check S2019RootFullDescentAll_of_effDescent
#check S2019RootIsStack_of_fullDescentAll
#check S2019CorrectedIdentityPresentation
#check S2019CorrectedIdentityPresentationData
#check S2019CorrectedFiniteEtale
#check S2019CorrectedFiniteEtaleAll
#check S2019CorrectedFiniteEtaleAll_iff
#check S2019CorrectedIdentityPresentationAll_of_finiteEtaleAll
#check S2019UniqFirstMissing_of_identityPresentations
#check S2019CorrectedFiniteEtaleAll_uniq
#check S2019CorrectedIdentityPresentation_toRecorded
#check S2019CorrectedFull_iff_missingHalf
#check S2019CorrectedFiniteEtale_toRecorded
#check S2019_noSchemaFromWitness
#check S2019_counterexample_identity_not_corrected
#check S2019_recorded_full_refuted
#check S2019CorrectedRootStackDatum
#check S2019CorrectedRootStackDatum.toRecorded
#check S2019CorrectedRootStackDatum.ofRecorded
#check S2019CorrectedRootStackMissing_iff
#check S2019CorrectedRootStack_supplies_recorded
#check S2019CorrectedRootStack_of_recorded
#check S2019CorrectedRootStack_witness_aut
#check S2019CorrectedRootStack_not_discreteFiber
#check S2019CorrectedRootStackMissing_implies_S1994
#check S2019RebasedRootStackRoute
#check S2019RebasedRootStackRoute_iff
#check S2019RebasedRootStackRoute_supplies_recorded
#check S2019RebasedRootStackRoute_uniq
#check S2019RebasedRootStackRoute_identityPresentations
#check S2019RebasedRootStackRoute_witness_aut

#print axioms S2019IsoCommaDescent_iff_essSurj
#print axioms S2019FullIsStack_iff_IsStack
#print axioms S2019RootFullIsStack_iff_fullDescentAll
#print axioms S2019RootIsStack_iff_fullDescentAll
#print axioms S2019RootFullDescentAll_iff_effDescent
#print axioms S2019FirstMissing_iff_IsStack
#print axioms S2019FirstMissing_iff_effDescent
#print axioms S2019RootFullDescentAll_effDescent
#print axioms S2019RootFullDescentAll_of_effDescent
#print axioms S2019RootIsStack_of_fullDescentAll
#print axioms S2019CorrectedFiniteEtaleAll_iff
#print axioms S2019CorrectedIdentityPresentationAll_of_finiteEtaleAll
#print axioms S2019UniqFirstMissing_of_identityPresentations
#print axioms S2019CorrectedFiniteEtaleAll_uniq
#print axioms S2019CorrectedIdentityPresentation_toRecorded
#print axioms S2019CorrectedFull_iff_missingHalf
#print axioms S2019CorrectedFiniteEtale_toRecorded
#print axioms S2019_noSchemaFromWitness
#print axioms S2019_counterexample_identity_not_corrected
#print axioms S2019_recorded_full_refuted
#print axioms S2019CorrectedRootStackDatum.toRecorded
#print axioms S2019CorrectedRootStackDatum.ofRecorded
#print axioms S2019CorrectedRootStackMissing_iff
#print axioms S2019CorrectedRootStack_supplies_recorded
#print axioms S2019CorrectedRootStack_of_recorded
#print axioms S2019CorrectedRootStack_witness_aut
#print axioms S2019CorrectedRootStack_not_discreteFiber
#print axioms S2019CorrectedRootStackMissing_implies_S1994
#print axioms S2019RebasedRootStackRoute_iff
#print axioms S2019RebasedRootStackRoute_supplies_recorded
#print axioms S2019RebasedRootStackRoute_uniq
#print axioms S2019RebasedRootStackRoute_identityPresentations
#print axioms S2019RebasedRootStackRoute_witness_aut

end LeanFormal.IUT.XiFPaper.S2019RebasedRootStackActual
