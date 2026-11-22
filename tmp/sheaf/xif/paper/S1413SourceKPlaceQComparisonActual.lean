import tmp.sheaf.xif.paper.S436KSideQVActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4FKDescentBridge
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# S1413: the q comparison diagram at the paper's section-designated K-place

Route A of the 2026-10-30 gap report asks for one bounded action: do not try to
prove that the two *independently chosen* K-places of S438/S605 coincide; either
transport by conjugacy or, better, instantiate the existing q transport
**directly at the K-place that the source section designates**, reading the
F-side source parameter at the F-place that actually sits under it.

This file does exactly that, and nothing else: no `FinalXiF` wrapper, no new
abstract interface, no weakened target, no added hypothesis on the final
inequality.

## The comparison figure (every entry is proved below)

Fix a source datum `T` and a bad moduli place `b : Bad (nativePlaceSelection T)`
(IUT I Definition 3.1(b); IUT I Example 3.2(iv), p. 71).

| component | object in this file | status |
|---|---|---|
| bad moduli place | `b.1` | source input |
| section-designated K-place | `sectionKPlace T b = kSidePlace T b = sectionFiniteLift P b.1` (S436; `SourcePlacePartitionReduction`) | actual |
| the F-side place under it | `sectionFPlace T b = fkDescentShadow P b.1`, and `comap (k := A.F) (sectionKPlace T b) = sectionFPlace T b` | actual, `rfl` |
| the clause-B F-place of S438 | `nativeFPlace T b = (nativeBadLift T).lift b` | actual |
| contractions to the moduli place | `comap (k := A.Fmod) sectionFPlace = b.1`, `comap (k := A.Fmod) nativeFPlace = b.1`, `comap (k := A.Fmod) sectionKPlace = b.1` | proved |
| F-side source parameter | `shadowQ T b`: the actual clause-B `SourceTateComparisonWitness` parameter at `sectionFPlace T b` | actual |
| completion map | `completionMapSection T b = completionMap (k := A.F) (sectionKPlace T b) : F_v ->+* K_w` | actual |
| K-side q parameter | `sectionQ T b = shadowQ T b`.map along `sectionKPlace T b` | actual |
| q equation | `(sectionQ T b).q = completionMapSection T b (shadowQ T b).q` | `rfl` |
| order law | `(sectionQ T b).order = eSource T b * (shadowQ T b).order` | proved |
| valuation law | `v (sectionQ T b).q = v (shadowQ T b).q ^ eSource T b` | proved |
| norm normalization | `localLogMagnitude (sectionQ) = (e * f) * localLogMagnitude (shadowQ)`, `orderNormalizedMagnitude (sectionQ) = e * orderNormalizedMagnitude (shadowQ)`, and at each level `localLogMagnitude = order * log (residueNormBase)` | proved |

`eSource T b = fkDescentSectionRamificationIndex P b.1` is the source section's
ramification index; `sectionRamificationIndex_eq_local` identifies it with the
library `localRamificationIndex` / `ramificationIdx'` used by S438.

## What the figure fixes, and what it does not

The *element* transport is the completion embedding, not a power: the K-side q is
the image of the F-side q, so the two parameters agree literally.  What scales is
the discrete order (`e`: `sectionQ_order`) and the canonical log-magnitude
(`e * f`: `sectionQ_localLogMagnitude_vs_shadow`); dividing the log-magnitude by
`log (residueNormBase)` removes the `f` and recovers the order at each level
(`sectionQ_orderNormalized_vs_shadow`).  Recorded so that `r`, `r * f` and
`r / e` are not silently interchanged (fourth gap of the report).

## Obligation table for the S436/S605 consumer

* supplied here: the q object at the paper's K-place, the two comap equations,
  the completion map, the q equation, the order law (with the *source* section
  ramification index), the valuation law and the norm normalization.
* `S1413ShadowEqualsNative` (the F-place identity
  `fkDescentShadow P b.1 = (nativeBadLift T).lift b`): **not proved and not
  assumed**.  `shadow_eq_of_place_eq` shows it is *implied* by S605/S618's
  K-place identity, hence strictly weaker; it is the F-side content of the two
  independent choices.
* `S1413SectionTateUniformization` (a `TateCurveComparison` of the base-changed
  curve at the paper's K-place with this q): **not available anywhere in the
  tree**; S436/S605 store it as a field.  No ambient/proxy substitute is used.
* `SectionTwoLRoot` (a `2l`-th root of the K-side q in the specified completion):
  **not constructed**.  No claim of the form "no completion has a root" is made;
  `two_l_dvd_order_of_root` and `l_dvd_ramification_of_root` give the exact
  arithmetic obstruction: a root forces `l | eSource`, i.e. `l` must divide the
  ramification index of the *specified* place, exactly as anticipated by S438.
* clause (c) is not consumed here: its `l`-torsion carrier does not by itself
  produce the `mu_{2l}` indeterminacy of the root, because `2 * l` is not an
  `l`-power.  The factor `2` is a separate Tate-torsion input (S494's gap).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The three actual places of the figure -/

/-- The actual `A.F`-place under the paper's section-designated K-place: the
F-shadow of the section lift of the bad moduli place `b.1`.  This is the F-side
place at which the source section puts its q-parameter. -/
abbrev sectionFPlace : NumberField.FinitePlace T.arithmetic.F :=
  fkDescentShadow (nativePlaceSelection T) b.1

/-- The actual `A.F`-place carrying the clause-B source parameter `qVFamily`
(S438's `nativeBadLift` lift). -/
abbrev nativeFPlace : NumberField.FinitePlace T.arithmetic.F :=
  (nativeBadLift T).lift b

/-- The paper's section-designated `A.K`-place above `b.1` (S436's `kSidePlace`). -/
abbrev sectionKPlace : NumberField.FinitePlace T.arithmetic.K :=
  kSidePlace (T := T) b

/-- The source section's ramification index at `b.1`. -/
abbrev eSource : Nat :=
  fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1

theorem sectionFPlace_comap :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (sectionFPlace T b) = b.1 :=
  fkDescentShadow_comap (nativePlaceSelection T) b.1

theorem nativeFPlace_comap :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (nativeFPlace T b) = b.1 :=
  (nativeBadLift T).lift_comap b

/-- The K-place contracts to the shadow F-place, definitionally. -/
theorem sectionKPlace_comap :
    NumberFieldFinitePlace.comap (k := T.arithmetic.F) (sectionKPlace T b) =
      sectionFPlace T b :=
  rfl

theorem sectionKPlace_over_moduli :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (sectionKPlace T b) = b.1 :=
  sectionFiniteLift_comap (nativePlaceSelection T) b.1

/-- The F-place of the source q and the paper's K-place contract to the *same*
bad moduli place: this is the only sense in which they are "the same place", and
it is what makes the comparison legal. -/
theorem sectionKPlace_over_same_moduli_place :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (sectionKPlace T b) =
      NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (nativeFPlace T b) := by
  rw [sectionKPlace_over_moduli, nativeFPlace_comap]

theorem sectionFPlace_over_same_moduli_place :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (sectionFPlace T b) =
      NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (nativeFPlace T b) := by
  rw [sectionFPlace_comap, nativeFPlace_comap]

theorem sectionKPlace_comap_comap :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        (NumberFieldFinitePlace.comap (k := T.arithmetic.F) (sectionKPlace T b)) = b.1 := by
  rw [sectionKPlace_comap, sectionFPlace_comap]

/-- Name reconciliation: the source section's ramification index is exactly the
library ramification index of the designated place over its contraction (the
quantity S438 writes as `ramificationIdx'`). -/
theorem sectionRamificationIndex_eq_local :
    eSource T b = ArithmeticQPilotBaseChange.localRamificationIndex (k := T.arithmetic.F) (sectionKPlace T b) :=
  rfl

/-! ## 2. The F-side source parameter at the paper's F-place -/

/-- The actual clause-B Tate comparison witness at the paper's F-place.  It uses
exactly the same clause-B input as `qVFamily`, but at the F-place determined by
the section instead of an arbitrary lift. -/
noncomputable def shadowWitness :
    SourceTateComparisonWitness T.arithmetic (sectionFPlace T b) :=
  Classical.choice
    (T.clauseB.q_comparison (sectionFPlace T b) (by
      rw [sectionFPlace_comap]
      exact b.2))

/-- The F-side source q parameter at the paper's F-place. -/
noncomputable def shadowQ : FinitePlaceQCandidate (sectionFPlace T b) :=
  (shadowWitness T b).parameter

theorem shadowQ_order_coprime : Nat.Coprime (shadowQ T b).order l.value :=
  (shadowWitness T b).order_coprime

/-! ## 3. The completion map and the K-side q at the designated place -/

/-- The actual completion embedding `F_v -> K_w` at the paper's K-place. -/
noncomputable def completionMapSection :
    Completion (sectionFPlace T b) →+* Completion (sectionKPlace T b) :=
  completionMap (k := T.arithmetic.F) (sectionKPlace T b)

theorem completionMapSection_apply (x : Completion (sectionFPlace T b)) :
    completionMapSection T b x =
      completionMap (k := T.arithmetic.F) (sectionKPlace T b) x :=
  rfl

/-- The actual K-side q parameter at the paper's designated K-place.  This is the
direct instantiation that replaces "prove the two arbitrary K-places equal". -/
noncomputable def sectionQ : FinitePlaceQCandidate (sectionKPlace T b) :=
  FinitePlaceQCandidate.map (k := T.arithmetic.F) (sectionKPlace T b) (shadowQ T b)

/-- The q equation: the K-side q is the completion image of the F-side source q.
This is an identity of *elements*, not a power and not a mere equivalence. -/
theorem sectionQ_q :
    (sectionQ T b).q = completionMapSection T b (shadowQ T b).q :=
  rfl

/-! ## 4. Order, valuation and norm normalization -/

/-- Order law at the designated place, with the source section ramification index. -/
theorem sectionQ_order :
    (sectionQ T b).order = eSource T b * (shadowQ T b).order :=
  fkDescent_order_map_sectionFiniteLift (nativePlaceSelection T) b.1 (shadowQ T b)

theorem sectionQ_order_local :
    (sectionQ T b).order =
      ArithmeticQPilotBaseChange.localRamificationIndex (k := T.arithmetic.F) (sectionKPlace T b) *
        (shadowQ T b).order := by
  rw [sectionQ_order, sectionRamificationIndex_eq_local]

/-- The valuation law at the designated place: the multiplicative valuation of
the K-side q is the F-side valuation raised to the ramification index of that
place over its contraction (identified with `eSource` by
`sectionRamificationIndex_eq_local`).  Stated in the exact shape of
`FinitePlaceQCandidate.valuation_map` at this place, keeping the contracted
place in the library's `comap` spelling. -/
theorem sectionQ_valuation :
    (Valued.v (sectionQ T b).q : WithZero (Multiplicative Int)) =
      (Valued.v (shadowQ T b : FinitePlaceQCandidate
          (NumberFieldFinitePlace.comap (k := T.arithmetic.F) (sectionKPlace T b))).q :
        WithZero (Multiplicative Int)) ^
        (NumberFieldFinitePlace.comap (k := T.arithmetic.F) (sectionKPlace T b)).maximalIdeal.asIdeal.ramificationIdx'
          (sectionKPlace T b).maximalIdeal.asIdeal :=
  FinitePlaceQCandidate.valuation_map (k := T.arithmetic.F) (sectionKPlace T b) (shadowQ T b)

/-- Valuation/norm normalization at the designated place: the canonical
completion norm of the K-side q is the residue-norm base of the K-place to the
power [##-exponent##]. -/
theorem sectionQ_qNorm :
    ‖(sectionQ T b).q‖ =
      residueNormBase (sectionKPlace T b) ^ (-(sectionQ T b).exponent) :=
  qNorm_eq_residueNormBase_zpow (sectionQ T b)

/-- Valuation/norm normalization in order form at the designated place. -/
theorem sectionQ_localLogMagnitude :
    localLogMagnitude (sectionQ T b) =
      ((sectionQ T b).order : Real) * Real.log (residueNormBase (sectionKPlace T b)) :=
  localLogMagnitude_eq_order_mul_log (sectionQ T b)

/-- The same normalization at the F-side source place. -/
theorem shadowQ_localLogMagnitude :
    localLogMagnitude (shadowQ T b) =
      ((shadowQ T b).order : Real) * Real.log (residueNormBase (sectionFPlace T b)) :=
  localLogMagnitude_eq_order_mul_log (shadowQ T b)

/-- Cross-level normalization: the canonical log-magnitude scales by the full
local degree `e * f`, not by `e`. -/
theorem sectionQ_localLogMagnitude_vs_shadow :
    ArithmeticQPilotLogVolume.localLogMagnitude (sectionQ T b) =
      (ArithmeticQPilotBaseChange.completionNormDegree (k := T.arithmetic.F) (sectionKPlace T b) : Real) *
        ArithmeticQPilotLogVolume.localLogMagnitude (shadowQ T b) := by
  change ArithmeticQPilotLogVolume.localLogMagnitude
      (FinitePlaceQCandidate.map (k := T.arithmetic.F) (sectionKPlace T b) (shadowQ T b)) =
    ((ArithmeticQPilotBaseChange.completionNormDegree (k := T.arithmetic.F) (sectionKPlace T b) : Nat) : Real) *
      ArithmeticQPilotLogVolume.localLogMagnitude (shadowQ T b)
  exact ArithmeticQPilotBaseChange.localLogMagnitude_map (k := T.arithmetic.F) (sectionKPlace T b) (shadowQ T b)

/-- Dividing the log-magnitude by the residue-norm logarithm removes the `f`:
the order-normalized magnitude scales by `e` alone. -/
theorem sectionQ_orderNormalized_vs_shadow :
    ArithmeticQPilotBaseChange.orderNormalizedMagnitude (sectionQ T b) =
      (eSource T b : Real) * ArithmeticQPilotBaseChange.orderNormalizedMagnitude (shadowQ T b) := by
  have h := ArithmeticQPilotBaseChange.orderNormalizedMagnitude_map (k := T.arithmetic.F)
    (sectionKPlace T b) (shadowQ T b)
  rw [sectionRamificationIndex_eq_local]
  exact h

/-- At each level the normalized magnitude *is* the discrete order: the two
readings are not interchangeable before this division. -/
theorem sectionQ_orderNormalized_eq_order :
    orderNormalizedMagnitude (sectionQ T b) = ((sectionQ T b).order : Real) :=
  orderNormalizedMagnitude_eq_order (sectionQ T b)

theorem shadowQ_orderNormalized_eq_order :
    orderNormalizedMagnitude (shadowQ T b) = ((shadowQ T b).order : Real) :=
  orderNormalizedMagnitude_eq_order (shadowQ T b)

/-! ## 5. The two remaining inputs for the S436 consumer, stated exactly -/

/-- The F-place identity that this construction does *not* prove: the paper's
section F-place is the clause-B F-place of `qVFamily`.  Both lie over `b.1`; a
moduli fibre of the contraction may contain several `A.F`-places, so this is a
genuine statement about the source data. -/
abbrev S1413ShadowEqualsNative : Prop :=
  sectionFPlace T b = nativeFPlace T b

/-- The K-side Tate uniformization at the paper's K-place.  Nothing in the tree
supplies a `TateCurveComparison` at a K-place; S436/S605 store it as a field, and
no ambient/proxy substitute is used here. -/
def S1413SectionTateUniformization : Prop :=
  Nonempty (TateCurveComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b))

/-- S605/S618's K-place identity implies the F-place identity, hence the F-place
obligation used here is strictly weaker than S605's `place_eq`.  The converse
fails in general (one F-place may have several K-places above it) and is not
needed by the construction. -/
theorem shadow_eq_of_place_eq
    (hplace : qVFamilyKLift T b = sectionKPlace T b) :
    S1413ShadowEqualsNative T b := by
  have h := congrArg (NumberFieldFinitePlace.comap (k := T.arithmetic.F)) hplace
  rw [qVFamilyKLift_comap] at h
  exact h.symm

/-- Order invariance of the clause-B parameter under a change of the F-place:
after the substitution both sides are `Classical.choice` of the same clause-B
proposition at the same place, so proof irrelevance gives the same witness.  The
places are variables so that the elimination is not dependent. -/
theorem parameter_order_congr
    {p q : NumberField.FinitePlace T.arithmetic.F}
    (hp : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) p ∈
      (nativePlaceSelection T).V_mod_bad)
    (hq : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) q ∈
      (nativePlaceSelection T).V_mod_bad)
    (h : p = q) :
    (Classical.choice (T.clauseB.q_comparison p hp)).parameter.order =
      (Classical.choice (T.clauseB.q_comparison q hq)).parameter.order := by
  cases h
  rfl

/-- If the two F-places coincide, the section-side q *is* the clause-B
`qVFamily` parameter, because both are `Classical.choice` of the same clause-B
proposition at the same place.  This is derived, not assumed. -/
theorem shadowQ_order_eq_of_shadow_eq
    (hF : S1413ShadowEqualsNative T b) :
    (shadowQ T b).order = (qVFamily T b).order :=
  parameter_order_congr (T := T) (p := sectionFPlace T b) (q := nativeFPlace T b)
    (h := hF)
    (by rw [sectionFPlace_comap]; exact b.2)
    (by rw [nativeFPlace_comap]; exact b.2)

/-- **The S436 K-side q_v object at the paper's designated place.**  Beyond this
file it needs exactly the F-place identity and the K-side Tate uniformization;
the order law is *derived* (with the source section ramification index), not
assumed, and the q object is the actual completion image, not an arbitrary
candidate. -/
noncomputable def kSideQVFamilySpecOfSection
    (hF : S1413ShadowEqualsNative T b)
    (uniformization : TateCurveComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b)) :
    KSideQVFamilySpec (T := T) (b := b) where
  kPlace := sectionKPlace T b
  kPlace_eq := rfl
  kCurve := kSideCurve (T := T)
  kCurve_eq := rfl
  q := sectionQ T b
  uniformization := uniformization
  fPlace := nativeFPlace T b
  fPlace_eq := rfl
  shadow_compatible := hF
  fOrder := (qVFamily T b).order
  fOrder_eq := rfl
  order_eq := by
    rw [sectionQ_order, shadowQ_order_eq_of_shadow_eq T b hF]

/-- Conditional existence of the paper's K-side q_v object from exactly the two
inputs above. -/
theorem kSideQVFamilyRequired_of_section
    (hF : S1413ShadowEqualsNative T b)
    (uniformization : TateCurveComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b)) :
    KSideQVFamilyRequired (T := T) (b := b) :=
  ⟨kSideQVFamilySpecOfSection T b hF uniformization⟩

/-! ## 6. The root descent at the designated place -/

/-- Exact missing root data at the paper's designated K-place: a `2l`-th root of
the K-side q *inside the specified completion*.  No root is fabricated and no
"no root exists" statement is made. -/
structure SectionTwoLRoot where
  root : Completion (sectionKPlace T b)
  root_pow : root ^ (2 * l.value) = (sectionQ T b).q

/-- The root-descent obligation at the paper's place, by name. -/
def SectionTwoLRootRequired : Prop := Nonempty (SectionTwoLRoot (T := T) (b := b))

/-- Nonzero elements of a completion have nonzero valuation. -/
theorem valuationElement_ne_zero {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K} (x : Completion place) (hx : x ≠ 0) :
    (Valued.v x : WithZero (Multiplicative Int)) ≠ 0 := by
  intro h
  exact hx (((Valued.v :
    Valuation (Completion place) (WithZero (Multiplicative Int))).map_eq_zero_iff).mp h)

/-- The additive valuation exponent of a nonzero element of a completion. -/
noncomputable def elementExponent {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K} (x : Completion place) (hx : x ≠ 0) : Int :=
  -Multiplicative.toAdd (WithZero.unzero (valuationElement_ne_zero x hx))

theorem elementExponent_eq_exponent {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K} (parameter : FinitePlaceQCandidate place)
    (h : parameter.q ≠ 0) :
    elementExponent parameter.q h = parameter.exponent :=
  rfl

theorem elementExponent_congr {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K} {x y : Completion place}
    (hxy : x = y) (hx : x ≠ 0) (hy : y ≠ 0) :
    elementExponent x hx = elementExponent y hy := by
  subst hxy
  rfl

/-- The additive exponent is additive under natural powers. -/
theorem elementExponent_pow {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K} (x : Completion place) (hx : x ≠ 0) (n : Nat) :
    elementExponent (x ^ n) (pow_ne_zero n hx) = (n : Int) * elementExponent x hx := by
  have hunzero :
      WithZero.unzero (valuationElement_ne_zero (x ^ n) (pow_ne_zero n hx)) =
        WithZero.unzero (valuationElement_ne_zero x hx) ^ n := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, WithZero.coe_pow]
    exact map_pow Valued.v x n
  rw [elementExponent, elementExponent, hunzero, Int.toAdd_pow]
  ring

/-- A `2l`-th root at the designated place forces `2l` to divide the K-side
order. -/
theorem two_l_dvd_order_of_root
    (root : Completion (sectionKPlace T b))
    (hroot : root ^ (2 * l.value) = (sectionQ T b).q) :
    2 * l.value ∣ (sectionQ T b).order := by
  have hroot_ne : root ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.mul_ne_zero (by norm_num) (Nat.Prime.ne_zero l.2))] at hroot
    exact (sectionQ T b).q_ne_zero hroot.symm
  have h1 : elementExponent (root ^ (2 * l.value))
        (pow_ne_zero (2 * l.value) hroot_ne) =
      ((2 * l.value : Nat) : Int) * elementExponent root hroot_ne :=
    elementExponent_pow (place := sectionKPlace T b) root hroot_ne (2 * l.value)
  have h2 : elementExponent (sectionQ T b).q (sectionQ T b).q_ne_zero =
      elementExponent (root ^ (2 * l.value)) (pow_ne_zero (2 * l.value) hroot_ne) :=
    elementExponent_congr (place := sectionKPlace T b) hroot.symm _ _
  have h3 : (sectionQ T b).exponent =
      elementExponent (sectionQ T b).q (sectionQ T b).q_ne_zero :=
    rfl
  have hexp : (sectionQ T b).exponent =
      ((2 * l.value : Nat) : Int) * elementExponent root hroot_ne := by
    rw [h3, h2, h1]
  have hpos : (0 : Int) < ((2 * l.value : Nat) : Int) * elementExponent root hroot_ne := by
    rw [← hexp]
    exact (sectionQ T b).exponent_pos
  have hnat : (0 : Int) < ((2 * l.value : Nat) : Int) := by
    have hlpos : 0 < l.value := l.prime.pos
    have : (0 : Nat) < 2 * l.value := Nat.mul_pos (by norm_num) hlpos
    exact_mod_cast this
  have hAle : 0 ≤ elementExponent root hroot_ne := by nlinarith
  refine ⟨(elementExponent root hroot_ne).toNat, ?_⟩
  show Int.toNat (sectionQ T b).exponent =
    2 * l.value * (elementExponent root hroot_ne).toNat
  rw [hexp, Int.toNat_mul (le_of_lt hnat) hAle, Int.toNat_natCast]

/-- **The exact arithmetic obstruction at the paper's place.**  A `2l`-th root of
the K-side q in the specified completion forces `l` to divide the ramification
index of that place.  Since the F-side order is prime to `l` (clause (c)), this
is the whole divisibility content of the root descent; the unit part and the
placement inside the designated completion remain separate. -/
theorem l_dvd_ramification_of_root
    (root : Completion (sectionKPlace T b))
    (hroot : root ^ (2 * l.value) = (sectionQ T b).q) :
    l.value ∣ eSource T b := by
  have h2l := two_l_dvd_order_of_root T b root hroot
  have hl : l.value ∣ (sectionQ T b).order :=
    Nat.dvd_trans ⟨2, by ring⟩ h2l
  have her : l.value ∣ eSource T b * (shadowQ T b).order := by
    rw [← sectionQ_order]
    exact hl
  exact (shadowQ_order_coprime T b).symm.dvd_of_dvd_mul_right her

/-! ## 7. Axiom audit (in-file, so that one run is the verification)

Each reported theorem must depend only on `propext`, `Classical.choice` and
`Quot.sound`. -/

#print axioms sectionKPlace_comap
#print axioms sectionQ_q
#print axioms sectionQ_order
#print axioms sectionQ_valuation
#print axioms sectionQ_qNorm
#print axioms sectionQ_localLogMagnitude_vs_shadow
#print axioms sectionQ_orderNormalized_vs_shadow
#print axioms shadow_eq_of_place_eq
#print axioms shadowQ_order_eq_of_shadow_eq
#print axioms kSideQVFamilyRequired_of_section
#print axioms two_l_dvd_order_of_root
#print axioms l_dvd_ramification_of_root

end LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual

end
