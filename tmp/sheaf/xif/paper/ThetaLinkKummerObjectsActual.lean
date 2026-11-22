import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitFactorizationProvider
import tmp.sheaf.xif.paper.KummerEvaluationArrowsActual2
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-!
# Actual Theta-link Kummer objects from strip equivalences

IUT III, Proposition 1.2, (iv), and Theorem 3.11, (ii), attach to a link of
F-prime-strips the Kummer isomorphism of the units / x-mu layers.  The concrete
repo data are the actual strip actions

  FPrimeStrip.unitsAction v : Pi v ->* MulAut (Mon v)^x

and an actual strip equivalence

  e : FPrimeStripEquiv upper lower.

From these data this file constructs, without an abstract choice:

* the quotient equivalence of the x-mu unit layers (torsion quotient);
* an actual TimesMuKummer.Isomorphism from the upper action to the lower
  action transported through e.isoPi;
* an actual KappaOrbitUnitsActionPairDatum for the pair;
* the production SourceTimesMuKummerLayer / SourceEvaluationUnitPortion and
  the resulting SourceKummerArrow / SourceEvaluationArrow from the actual
  Hodge-theater strip links.

The remaining source datum is the profinite topology on the product group used
by OpenSubgroup/invariantImage; FPrimeStrip only stores Group, not
TopologicalSpace.  That topology is an explicit parameter, not fabricated.
The IPL factorization equality and the Kummer-evaluation square commutation are
recorded as exact missing fields at the end; no inequality is asserted.

No arbitrary action, trivial layer, PUnit/True, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ThetaLinkKummerObjectsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.KummerEvaluationArrowsActual2

universe uG uv ua upi umon ui

variable {V : Type uv}
variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The common product group of a strip pair. -/
abbrev PairGroup (upper lower : FPrimeStrip V) : Type _ :=
  (v : V) -> upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v

/-- The actual lower action transported through a strip equivalence, replacing
the lower projection by the actual e.isoPi image of the upper projection. -/
noncomputable def transportedLowerAction
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    (v : V) : PairGroup upper lower →* MulAut ((lower.Mon v)ˣ) :=
  (lower.unitsAction v).comp
    ((e.isoPi v).toMonoidHom.comp (FPrimeStrip.pairFactorizationUpper upper lower v))

/-- The torsion-quotient equivalence of the x-mu unit layers induced by an
actual strip equivalence. -/
noncomputable def xMuQuotientEquiv
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower) (v : V) :
    TimesMuQuotient ((upper.Mon v)ˣ) ≃* TimesMuQuotient ((lower.Mon v)ˣ) :=
  TimesMuQuotient.congr (Units.mapEquiv (e.isoMon v))

/-- The actual upper x-mu action is the upper strip action through the upper
factorization. -/
theorem pairUnitsActionUpper_eq
    (upper lower : FPrimeStrip V) (v : V) :
    FPrimeStrip.pairUnitsActionUpper upper lower v =
      (upper.unitsAction v).comp
        (FPrimeStrip.pairFactorizationUpper upper lower v) := rfl

/-- The quotient equivalence is equivariant for the upper action and the
transported lower action.  This is the unit-level content of the strip
equivalence compatAction, passed through the torsion quotient. -/
theorem xMuQuotientEquiv_equivariant
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower) (v : V)
    (g : PairGroup upper lower) (x : TimesMuQuotient ((upper.Mon v)ˣ)) :
    xMuQuotientEquiv upper lower e v
        (TimesMuQuotient.action
          (FPrimeStrip.pairUnitsActionUpper upper lower v) g x) =
      TimesMuQuotient.action
        (transportedLowerAction upper lower e v) g
        (xMuQuotientEquiv upper lower e v x) := by
  refine Quotient.inductionOn x ?_
  intro u
  change xMuQuotientEquiv upper lower e v
      (TimesMuQuotient.action (FPrimeStrip.pairUnitsActionUpper upper lower v) g
        (TimesMuQuotient.quotientMap u)) =
    TimesMuQuotient.action (transportedLowerAction upper lower e v) g
      (xMuQuotientEquiv upper lower e v (TimesMuQuotient.quotientMap u))
  rw [TimesMuQuotient.action_quotientMap, TimesMuQuotient.congr_quotientMap,
    TimesMuQuotient.congr_quotientMap, TimesMuQuotient.action_quotientMap]
  apply congrArg TimesMuQuotient.quotientMap
  apply Units.ext
  simp only [Units.coe_mapEquiv, FPrimeStrip.pairUnitsActionUpper_apply,
    FPrimeStrip.unitsAction_val, transportedLowerAction,
    MonoidHom.comp_apply]
  exact e.compatAction v (g v).1 (u : upper.Mon v)

/-- The actual lower Kummer isomorphism obtained from the actual strip
equivalence.  The source action is the actual upper pair action; the target
action is the transported actual lower action. -/
noncomputable def kappaLowerOfStripEquiv
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower) (v : V)
    [TopologicalSpace (PairGroup upper lower)] :
    TimesMuKummer.Isomorphism
      (FPrimeStrip.pairUnitsActionUpper upper lower v)
      (transportedLowerAction upper lower e v) where
  equiv := xMuQuotientEquiv upper lower e v
  equivariant := xMuQuotientEquiv_equivariant upper lower e v
  invariantImage := by
    intro H
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases (TimesMuKummer.mem_invariantImage_iff
        (FPrimeStrip.pairUnitsActionUpper upper lower v) H x).mp hx with
        ⟨u, hu, rfl⟩
      refine (TimesMuKummer.mem_invariantImage_iff
        (transportedLowerAction upper lower e v) H
        (xMuQuotientEquiv upper lower e v
          (TimesMuQuotient.quotientMap u))).mpr
        ⟨Units.mapEquiv (e.isoMon v) u, ?_, ?_⟩
      · intro g
        apply Units.ext
        simp only [Units.coe_mapEquiv, FPrimeStrip.unitsAction_val,
          transportedLowerAction, MonoidHom.comp_apply]
        rw [← e.compatAction v (g v).1 (u : upper.Mon v)]
        exact congrArg (e.isoMon v) (hu g)
      · rfl
    · intro hy
      obtain ⟨u, hu⟩ := TimesMuQuotient.quotientMap_surjective
        ((xMuQuotientEquiv upper lower e v).symm y)
      refine ⟨(xMuQuotientEquiv upper lower e v).symm y, ?_, ?_⟩
      · refine (TimesMuKummer.mem_invariantImage_iff
          (FPrimeStrip.pairUnitsActionUpper upper lower v) H
          ((xMuQuotientEquiv upper lower e v).symm y)).mpr
          ⟨u, ?_, hu⟩
        intro g
        apply (xMuQuotientEquiv upper lower e v).injective
        rw [xMuQuotientEquiv_equivariant upper lower e v g
          ((xMuQuotientEquiv upper lower e v).symm y)]
        rw [MulEquiv.apply_symm_apply]
        exact TimesMuKummer.invariantImage_fixed
          (transportedLowerAction upper lower e v) H hy g
      · exact (xMuQuotientEquiv upper lower e v).apply_symm_apply y

/-- The actual KappaOrbitUnitsActionPairDatum from an actual strip equivalence
and the actual upper action; the lower factor is the transported actual
e.isoPi-image. -/
noncomputable def pairDatumOfStripEquiv
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    [TopologicalSpace (PairGroup upper lower)] :
    KappaOrbitUnitsActionPairDatum (PairGroup upper lower) upper lower where
  sourceUnits := fun v => (upper.Mon v)ˣ
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := fun v => FPrimeStrip.pairUnitsActionUpper upper lower v
  factorUpper := fun v => FPrimeStrip.pairFactorizationUpper upper lower v
  factorLower := fun v =>
    (e.isoPi v).toMonoidHom.comp
      (FPrimeStrip.pairFactorizationUpper upper lower v)
  kappaUpper := fun v =>
    TimesMuKummer.Isomorphism.refl
      (FPrimeStrip.pairUnitsActionUpper upper lower v)
  kappaLower := fun v => kappaLowerOfStripEquiv upper lower e v

/-- The actual source Kummer layer from the actual strip equivalence. -/
noncomputable def layerOfStripEquiv
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    [TopologicalSpace (PairGroup upper lower)] :
    SourceTimesMuKummerLayer (PairGroup upper lower) upper lower :=
  layerOfPair (pairDatumOfStripEquiv upper lower e)

/-- The actual source Kummer arrow from the actual strip isomorphism and the
actual Kummer layer. -/
noncomputable def kummerArrowOfStripEquiv
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    [TopologicalSpace (PairGroup upper lower)] :
    SourceKummerArrow (PairGroup upper lower) upper lower :=
  sourceKummerArrowOfLayer e (layerOfStripEquiv upper lower e)

/-- The actual source evaluation unit portion from the same pair datum. -/
noncomputable def evaluationUnitPortionOfStripEquiv
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    [TopologicalSpace (PairGroup upper lower)] :
    SourceEvaluationUnitPortion (PairGroup upper lower) upper lower :=
  evalPortionOfPair (pairDatumOfStripEquiv upper lower e)

/-- The actual source evaluation arrow from the actual strip isomorphism and the
actual unit portion. -/
noncomputable def evaluationArrowOfStripEquiv
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    [TopologicalSpace (PairGroup upper lower)] :
    SourceEvaluationArrow (PairGroup upper lower) upper lower :=
  sourceEvaluationArrowOfUnitPortion e
    (evaluationUnitPortionOfStripEquiv upper lower e)

/-! ## Actual source-strip instances

The actual Hodge-theater links supply the strip equivalences; the only extra
datum is the topology on the product group.  This is not fabricated: it is an
explicit parameter below. -/

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

abbrev S00 : FPrimeStrip V := I.primeStripAt 0 0

abbrev S01 : FPrimeStrip V := I.primeStripAt 0 1

abbrev S10 : FPrimeStrip V := I.primeStripAt 1 0

abbrev S11 : FPrimeStrip V := I.primeStripAt 1 1

/-- The actual S00 -> S01 strip equivalence from I.linkAt. -/
def actualKummerStripIso : FPrimeStripEquiv (S00 (I := I)) (S01 (I := I)) :=
  (I.linkAt 0 0 0 1).primeStripEquiv

/-- The actual S01 -> S11 strip equivalence from I.linkAt. -/
def actualEvaluationStripIso : FPrimeStripEquiv (S01 (I := I)) (S11 (I := I)) :=
  (I.linkAt 0 1 1 1).primeStripEquiv

/-- The actual Kummer arrow S00 -> S01, from the Hodge-theater link and the
actual upper strip actions, conditional on the source topology. -/
noncomputable def actualKummerArrowS00S01
    [TopologicalSpace (PairGroup (S00 (I := I)) (S01 (I := I)))] :
    SourceKummerArrow (PairGroup (S00 (I := I)) (S01 (I := I)))
      (S00 (I := I)) (S01 (I := I)) :=
  kummerArrowOfStripEquiv (S00 (I := I)) (S01 (I := I))
    (actualKummerStripIso (I := I))

/-- The actual evaluation arrow S01 -> S11, from the Hodge-theater link and the
actual unit actions, conditional on the source topology. -/
noncomputable def actualEvaluationArrowS01S11
    [TopologicalSpace (PairGroup (S01 (I := I)) (S11 (I := I)))] :
    SourceEvaluationArrow (PairGroup (S01 (I := I)) (S11 (I := I)))
      (S01 (I := I)) (S11 (I := I)) :=
  evaluationArrowOfStripEquiv (S01 (I := I)) (S11 (I := I))
    (actualEvaluationStripIso (I := I))

/-! ## Exact missing fields

1. The profinite topology on PairGroup is not carried by FPrimeStrip; the
   constructions above take it as an explicit parameter.  Without it no
   OpenSubgroup/invariantImage object exists.
2. A single common topological group G acting on all four corner strips is not
   supplied; the source only gives the local groups Pi v and the actual links.
3. The IPL factorization equality
   inputLink = (inv lowerHorizontal1) >> (inv lowerHorizontal2) >> kummer >>
   evaluation, and the Kummer-evaluation square commutation, are not derivable
   from strip equivalences alone; they are the exact missing source fields of
   Theorem 3.11, (iii), (a)--(d) / Remark 3.11.1, (iii).
-/

def MissingPairTopology
    (upper lower : FPrimeStrip V) : Prop :=
  Nonempty (TopologicalSpace (PairGroup upper lower))

end LeanFormal.IUT.XiFPaper.ThetaLinkKummerObjectsActual

end