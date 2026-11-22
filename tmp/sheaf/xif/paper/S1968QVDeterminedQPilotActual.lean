import tmp.sheaf.xif.paper.S1960QPilotAnchorActual
import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree

/-!
# S1968: the actual q_v-determined q-pilot object and the exact first missing of R6

## The obligation left by S1960

R6 of LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
(lines 74--75) is the identification of the reduced q-pilot anchor with the
paper's q-pilot F^boxplus-triangleright-x-mu-prime-strip of IUT III,
Definition 3.8, (i).  S1960 (S1960QPilotAnchorActual) constructed the
reduced anchor

  reducedQPilotAnchor D = sourceQPilotStrip (S1895PaperO D).boundary
    = (S1895PaperO D).strip = S1895Core I = (paperInput D).fPrimeStripAt 1 0
    = lgpStrip D = (paperFullLogKummerUQ D).evaluationSquare.lowerLeft

together with the canonical times-mu lift reducedQPilotTimesMu D and the
reduced self-identification reducedAnchorIdentification D; it recorded the
paper-side strip as missing and parameterized the R6 interface

  QPilotAnchorIdentification D (paperStrip : SourceFTimesMuPrimeStrip PaperV)

by it.  This file resolves the data question behind that parameter.

## What this file constructs (all actual, kernel-checked)

1. **The actual q_v family.**  At every bad place b of the S1527/S1895
   input, paperQV D b is the actual Definition 3.1(b)(c) q-parameter
   (paperInput D).initial.reduction.qParameter b; it is nonzero, contracting
   (norm < 1), and log (norm q) < 0.  Its actual completed-DVR order is
   paperQVOrder D b, the order of the actual completion q candidate at the
   F-place over b; it equals the S1487/S1391 order S1487Cand.order (S1527),
   and |log (q_b)| = order_b * log 5.

2. **The q-pilot object of IUT III, Definition 3.8, (i), at the object level.**
   The q-pilot object is the arithmetic divisor of the zero locus of the
   q_v, in the global realified Frobenioid C^boxplus_mod.  The latter is the
   actual S1927 object paperGlobalRealifiedFrobenioid D; its divisor monoid is
   the actual realified effective divisor monoid
   (HeightOneSpectrum O_Fmod ->_0 NNReal) x (InfinitePlace Fmod -> NNReal)
   (S1927).  The divisor group used for degrees here is the actual
   IUTIVArithmeticDivisor (PaperFmod D) of IUT IV, Definition 1.9, with
   deg = sum_v c_v * weight v and weight (.finite v) = log (absNorm v).

   * paperQPilotDivisor D is the order-weighted divisor supported on the
     actual bad base prime, with coefficients equal to the actual orders
     paperQVOrder D b (the bad family of the S1280/S1527 input is the
     singleton over the Gaussian place above 5, so the divisor sum over the
     bad places is the single displayed term).
   * paperQPilotDivisor_deg_eq_source : the degree of paperQPilotDivisor D is
     sum_b |log q_b|; through S1527 this is order_C3 * log 5.
   * paperQPilotLogVolume D = -deg (paperQPilotDivisor D), which is the
     actual source scalar sourceQPilotSignedLog, equal to
     -localLogMagnitude S1487Cand = -order_C3 * log 5 < 0: the paper's
     q-pilot log-volume -|log q|.
   * paperQPilotDivisor_deg_pos and the support statement record that this
     q-pilot object is nontrivial and supported exactly on the bad base prime.
   * QVDeterminedQPilotObject D packages the divisor, its degree and the
     log-volume with the equalities that witness the q_v-determination
     (paperQVOrder_abs_log, paperQVOrder_eq_abs_log_div: the coefficient is
     |log q_b| / log 5).

3. **The R6 interface, re-exported for the paper strip.**  R6Proper D P is
   Nonempty (QPilotAnchorIdentification D P).  The exact reduction
   r6Proper_iff is S1960's s1960_r6_exact_reduction, and
   r6Proper_of_equivalence converts a times-mu equivalence from the reduced
   anchor's canonical lift to the paper strip into the R6 identification.

## The exact first missing (R6 proper remains open)

R6 needs the paper-side times-mu strip *arising from* this q-pilot object
(IUT III, Definition 3.8, (i); IUT II, Definition 4.9, (viii), the
"associated pilot object" of an F^boxplus-triangleright-x-mu-prime-strip).
The first missing is a **definition**, not a proposition:

* (a) the paper-side paperQPilotFTimesMuStrip D : SourceFTimesMuPrimeStrip
  PaperV constructed from the q-pilot object paperQPilotDivisor D, together
  with
* (b) the identification of its associated pilot object with
  paperQPilotDivisor D.

Neither exists in the tree.  SourceFTimesMuPrimeStrip has no field for a
global arithmetic divisor or a pilot object, its only constructor is
SourceFTimesMuPrimeStrip.canonical, and the only F-prime-strips available
from an OriginalInput are the Hodge-theater strips I.fPrimeStripAt n m.  In
the concrete S1487 model those are the shear strips S1487Strip n m, whose
value monoid is the constant SourceHaarActualValueMonoid; no functor from the
global realified Frobenioid (or from an arithmetic divisor) to a prime strip is
constructed anywhere in the tree.  Consequently no honest inhabitant of
QPilotAnchorIdentification D P for the paper strip P can be produced here,
and this file does **not** declare a paper-side type, an arbitrary inhabitant,
a free Prop slot or a Nonempty gate.

## Obstructions proved here (why no available strip can be R6)

(i) **The reduced anchor's times-mu layer is trivial.**  The anchor's value
monoid is SourceHaarActualValueMonoid = Multiplicative {x : Real // x <= 0};
its unit group is trivial (x <= 0 and -x <= 0 force x = 0), hence so is
(reducedQPilotTimesMu D).timesMu v for every v.  It follows that every
candidate paper strip satisfying the R6 interface has subsingleton times-mu
fibers at every place (r6Proper_forces_trivial_timesMu).  The paper q-pilot
x-mu layer is precisely the q_v-determined unit layer, so the present
reduced value/unit model cannot host a faithful R6 identification: the missing
definition must also change the value/unit model, not merely add a strip.

(ii) **The tree's strips are q_v-blind.**  Replacing only the initial theta
data of the S1527 shear input (keeping the actual Hodge-theater family) leaves
I.fPrimeStripAt n m definitionally unchanged (withInitial,
fPrimeStripAt_withInitial); the concrete witness is S1487FaithfulInput vs
S1487TwoPlaceInput: same (1,0) strip, different q-pilot log-volumes
(candidate_blind, qPilot_scalar_differs).  Hence no strip available from the
tree can be certified as the q_v-determined paper q-pilot strip.

## Honest scope

No sorry, admit, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
assumption-only Nonempty gate is used.  The classical inputs are exactly those
already carried by S1895/S1958 (propext, Classical.choice, Quot.sound), see the
axiom probes at the end.  R6 proper is **not** claimed closed; the first
missing is the definition (a)/(b) above.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange

local instance s1968GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1968FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

namespace LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual

/-! ## 0. The actual q_v data of the S1895 paper input -/

/-- The actual q_v at a bad place of the S1895/S1527 input: the Definition
3.1(b)(c) q-parameter.  These are the scalar q_v of the S1280 Gaussian bad
family; S1527 computes q_v = (1/5) ^ order_C3 and
|log q_v| = order_C3 * log 5 = localLogMagnitude S1487Cand. -/
noncomputable def paperQV (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : ℝ :=
  (paperInput D).initial.reduction.qParameter b

theorem paperQV_eq_qParameter (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    paperQV D b = (paperInput D).initial.reduction.qParameter b := rfl

theorem paperQV_ne_zero (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : paperQV D b ≠ 0 :=
  (paperInput D).initial.reduction.qParameter_nonzero b

theorem paperQV_norm_lt_one (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : ‖paperQV D b‖ < 1 :=
  (paperInput D).initial.reduction.qParameter_contracting b

/-- The actual bad q-parameters are contracting, so their logs are negative. -/
theorem paperQV_log_neg (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : Real.log ‖paperQV D b‖ < 0 :=
  Real.log_neg (norm_pos_iff.mpr (paperQV_ne_zero D b)) (paperQV_norm_lt_one D b)

/-- The actual completed-DVR order of the q candidate at the F-place over the
bad place b (the exponent of the q parameter).  This is the coefficient of the
q-pilot divisor. -/
noncomputable def paperQVOrder (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : ℕ :=
  (badPlaceQCandidate (S1280Selection D.l) b).order

/-- The actual order equals the S1487/S1391 order order_C3 (S1527). -/
theorem paperQVOrder_eq_orderC3 (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    paperQVOrder D b = S1487Cand.order :=
  S1527_badPlaceQCandidate_order_eq D.l b

theorem paperQVOrder_pos (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : 0 < paperQVOrder D b := by
  rw [paperQVOrder_eq_orderC3]
  exact S1487Cand.order_pos

/-- **The q_v determines the order**: |log q_b| = order_b * log 5. -/
theorem paperQVOrder_abs_log (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    |Real.log (paperQV D b)| = (paperQVOrder D b : ℝ) * Real.log 5 := by
  have h1 : paperQV D b = (S1280ReductionClause D.l).qParameter b := rfl
  rw [h1, S1527_abs_log_qParameter]
  congr 1
  have h2 : S1527OrderC3 = paperQVOrder D b :=
    (S1527_badPlaceQCandidate_order_eq D.l b).symm
  exact_mod_cast h2

/-- Equivalently, the order is the normalized absolute log of the actual q_v. -/
theorem paperQVOrder_eq_abs_log_div (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (paperQVOrder D b : ℝ) = |Real.log (paperQV D b)| / Real.log 5 := by
  rw [paperQVOrder_abs_log]
  have hlog : Real.log 5 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- A chosen bad place: the S1280 bad family is the singleton over the actual
Gaussian place above 5, so this choice is the unique bad place. -/
noncomputable def paperQVBad0 (D : S1895PaperInput) :
    (paperInput D).initial.badPlaces :=
  S1527Bad0 D.l

/-! ## 1. The q-pilot object of IUT III, Definition 3.8, (i) -/

/-- The weight of the actual bad base prime in the arithmetic divisor group:
log (absNorm v) = log 5, because the bad place is the concrete Gaussian place
above 5 (its residue field is ZMod 5). -/
theorem paperBadBasePlace_weight (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    IUTIVPlace.weight (PaperFmod D)
      (IUTIVPlace.finite (paperBadBasePlace D b)) = Real.log 5 := by
  have hplace : b.1 = S1487FivePlace.val := by
    have hb := S1527_bad_val_eq D.l b
    rw [show S1487FivePlace.val = concreteGaussianFivePlace from rfl]
    exact hb
  have hres : residueNormBase b.1 = 5 := by
    rw [hplace]
    exact S1487_residueNormBase_five
  have hweight : IUTIVPlace.weight (PaperFmod D)
      (IUTIVPlace.finite (paperBadBasePlace D b)) =
        Real.log (residueNormBase b.1) := rfl
  rw [hweight, hres]

/-- **The actual q-pilot arithmetic divisor** determined by the q_v: the zero
locus of the q_v, with the actual completed-DVR orders as coefficients, as an
element of the realified arithmetic divisor group of the base field Fmod.
The bad family of the S1280/S1527 input is the singleton over the concrete
Gaussian place above 5, so the divisor sum over the bad places is the
displayed single term. -/
noncomputable def paperQPilotDivisor (D : S1895PaperInput) :
    IUTIVArithmeticDivisor (PaperFmod D) :=
  Finsupp.single (IUTIVPlace.finite (F := PaperFmod D)
      (paperBadBasePlace D (paperQVBad0 D)))
    ((paperQVOrder D (paperQVBad0 D) : ℝ))

/-- The coefficient of the q-pilot divisor at the bad base prime is the actual
order of the q_v. -/
theorem paperQPilotDivisor_apply (D : S1895PaperInput) :
    paperQPilotDivisor D
        (IUTIVPlace.finite (paperBadBasePlace D (paperQVBad0 D))) =
      (paperQVOrder D (paperQVBad0 D) : ℝ) := by
  rw [paperQPilotDivisor, Finsupp.single_eq_same]

/-- **The degree of the actual q-pilot divisor is |log q|**: it is
sum_b |log q_b| = order_C3 * log 5 (S1527). -/
theorem paperQPilotDivisor_deg_eq_source (D : S1895PaperInput) :
    IUTIVArithmeticDivisor.deg (F := PaperFmod D) (paperQPilotDivisor D) =
      sourceBadQAbsLog (paperInput D).initial := by
  rw [paperQPilotDivisor]
  change IUTIVArithmeticDivisor.degLinearMap (PaperFmod D)
      (Finsupp.single (IUTIVPlace.finite (paperBadBasePlace D (paperQVBad0 D)))
        ((paperQVOrder D (paperQVBad0 D) : ℝ))) = _
  rw [IUTIVArithmeticDivisor.deg_single]
  rw [paperBadBasePlace_weight]
  have hinit : (paperInput D).initial =
      S1527SourceData D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
        D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat D.hcusCompat := rfl
  rw [hinit, S1527_sourceBadQAbsLog]
  show (paperQVOrder D (paperQVBad0 D) : ℝ) * Real.log 5 =
    (S1487Cand.order : ℝ) * Real.log 5
  rw [paperQVOrder_eq_orderC3]

/-- The q-pilot divisor has positive degree. -/
theorem paperQPilotDivisor_deg_pos (D : S1895PaperInput) :
    0 < IUTIVArithmeticDivisor.deg (F := PaperFmod D) (paperQPilotDivisor D) := by
  rw [paperQPilotDivisor_deg_eq_source]
  exact sourceBadQAbsLog_pos_of_nonempty (paperInput D).initial ⟨paperQVBad0 D⟩

/-- **The q-pilot log-volume -|log q|**, as the negative degree of the actual
q-pilot divisor. -/
noncomputable def paperQPilotLogVolume (D : S1895PaperInput) : ℝ :=
  -sourceBadQAbsLog (paperInput D).initial

theorem paperQPilotLogVolume_eq_signedLog (D : S1895PaperInput) :
    paperQPilotLogVolume D = sourceQPilotSignedLog (paperInput D).initial := rfl

theorem paperQPilotLogVolume_eq_neg_deg (D : S1895PaperInput) :
    paperQPilotLogVolume D =
      - IUTIVArithmeticDivisor.deg (F := PaperFmod D) (paperQPilotDivisor D) := by
  rw [paperQPilotLogVolume, paperQPilotDivisor_deg_eq_source]

/-- The q-pilot log-volume is -order_C3 * log 5 = -|log q| (S1527). -/
theorem paperQPilotLogVolume_eq_orderC3 (D : S1895PaperInput) :
    paperQPilotLogVolume D = -((S1487Cand.order : ℝ) * Real.log 5) := by
  rw [paperQPilotLogVolume]
  have hinit : (paperInput D).initial =
      S1527SourceData D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
        D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat D.hcusCompat := rfl
  rw [hinit, S1527_sourceBadQAbsLog, S1527OrderC3_eq]

/-- The q-pilot log-volume is literally the negative of the actual S1487/S1391
completion log magnitude. -/
theorem paperQPilotLogVolume_eq_neg_localLogMagnitude (D : S1895PaperInput) :
    paperQPilotLogVolume D = -localLogMagnitude S1487Cand := by
  rw [paperQPilotLogVolume]
  have hinit : (paperInput D).initial =
      S1527SourceData D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
        D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat D.hcusCompat := rfl
  rw [hinit, S1527_sourceBadQAbsLog_eq_localLogMagnitude]

/-- The paper q-pilot log-volume is strictly negative. -/
theorem paperQPilotLogVolume_neg (D : S1895PaperInput) :
    paperQPilotLogVolume D < 0 := by
  rw [paperQPilotLogVolume_eq_orderC3]
  have hlog : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have horder : 0 < (S1487Cand.order : ℝ) := by
    exact_mod_cast S1487Cand.order_pos
  nlinarith

/-- The actual q_v-determined q-pilot object of IUT III, Definition 3.8, (i):
the order-weighted arithmetic divisor of the zero locus of the q_v in the
global realified Frobenioid, its degree |log q| and its log-volume -|log q|.
This is the **object**; it is not the paper's
F^boxplus-triangleright-x-mu-prime-strip (that strip is the exact first
missing, see the module docstring). -/
structure QVDeterminedQPilotObject (D : S1895PaperInput) where
  /-- the q-pilot arithmetic divisor determined by the actual q_v -/
  divisor : IUTIVArithmeticDivisor (PaperFmod D)
  /-- it is the zero-locus divisor with the actual orders -/
  divisor_eq : divisor = paperQPilotDivisor D
  /-- its degree is sum_b |log q_b| -/
  degree : ℝ
  degree_eq : degree =
    IUTIVArithmeticDivisor.deg (F := PaperFmod D) (paperQPilotDivisor D)
  degree_eq_abs_sum : degree = sourceBadQAbsLog (paperInput D).initial
  /-- the paper q-pilot log-volume -|log q| -/
  logVolume : ℝ
  logVolume_eq : logVolume = paperQPilotLogVolume D
  logVolume_eq_neg_degree : logVolume = -degree

/-- The q_v-determined q-pilot object is inhabited for every S1895 input. -/
noncomputable def qvDeterminedQPilotObject (D : S1895PaperInput) :
    QVDeterminedQPilotObject D where
  divisor := paperQPilotDivisor D
  divisor_eq := rfl
  degree := IUTIVArithmeticDivisor.deg (F := PaperFmod D) (paperQPilotDivisor D)
  degree_eq := rfl
  degree_eq_abs_sum := paperQPilotDivisor_deg_eq_source D
  logVolume := paperQPilotLogVolume D
  logVolume_eq := rfl
  logVolume_eq_neg_degree := paperQPilotLogVolume_eq_neg_deg D

theorem qvDeterminedQPilotObject_exists (D : S1895PaperInput) :
    Nonempty (QVDeterminedQPilotObject D) :=
  ⟨qvDeterminedQPilotObject D⟩

theorem qvDeterminedQPilotObject_divisor (D : S1895PaperInput) :
    (qvDeterminedQPilotObject D).divisor = paperQPilotDivisor D := rfl

theorem qvDeterminedQPilotObject_logVolume (D : S1895PaperInput) :
    (qvDeterminedQPilotObject D).logVolume =
      sourceQPilotSignedLog (paperInput D).initial := rfl

/-! ## 2. The R6 interface for a paper-side strip -/

/-- R6 proper, as a predicate on a candidate paper-side q-pilot times-mu strip:
the reduced q-pilot anchor is identified with the paper strip.  It is the
interface of S1960, parameterized by the paper strip because that strip is not
defined in the tree. -/
def R6Proper (D : S1895PaperInput)
    (paperStrip : SourceFTimesMuPrimeStrip PaperV) : Prop :=
  Nonempty (QPilotAnchorIdentification D paperStrip)

/-- R6 proper is exactly the nonemptiness of the times-mu equivalence class
(S1960's exact reduction). -/
theorem r6Proper_iff (D : S1895PaperInput)
    (paperStrip : SourceFTimesMuPrimeStrip PaperV) :
    R6Proper D paperStrip ↔
      Nonempty (SourceFTimesMuPrimeStripEquivalence
        (reducedQPilotTimesMu D) paperStrip) :=
  s1960_r6_exact_reduction D paperStrip

/-- A times-mu equivalence from the reduced anchor's canonical lift to the
paper strip gives the R6 identification.  This is the last step that the
missing definition of the paper strip has to feed. -/
theorem r6Proper_of_equivalence (D : S1895PaperInput)
    (paperStrip : SourceFTimesMuPrimeStrip PaperV)
    (e : SourceFTimesMuPrimeStripEquivalence (reducedQPilotTimesMu D) paperStrip) :
    R6Proper D paperStrip :=
  (s1960_r6_exact_reduction D paperStrip).mpr ⟨e⟩

/-- A full poly-isomorphism is of course also an R6 identification. -/
theorem r6Proper_of_fullPolyIso (D : S1895PaperInput)
    (paperStrip : SourceFTimesMuPrimeStrip PaperV)
    (phi : SourceFTimesMuPrimeStripFullPolyIsomorphism
      (reducedQPilotTimesMu D) paperStrip) :
    R6Proper D paperStrip :=
  ⟨phi⟩

/-- The reduced self-identification inhabits the R6 interface at the reduced
anchor's own lift.  This is S1960's qPilotAnchorSelfIdentification; it is
**not** R6, because the paper side is the reduced anchor itself. -/
theorem r6Proper_reducedSelf (D : S1895PaperInput) :
    R6Proper D (reducedQPilotTimesMu D) :=
  ⟨qPilotAnchorSelfIdentification D⟩

/-! ## 3. The reduced anchor's times-mu layer is trivial

The value monoid of the reduced anchor is SourceHaarActualValueMonoid, the
nonpositive reals under addition (multiplicatively).  Its unit group is
trivial, hence the whole x-mu (times-mu) layer of the reduced anchor is
trivial.  This is an actual property of the S1487 shear strip on which the
reduced anchor is based, and it is the reason the available reduced model
cannot host a faithful R6 identification. -/

/-- The unit group of the concrete nonpositive value monoid is trivial. -/
instance instSubsingletonSourceHaarUnits :
    Subsingleton ((SourceHaarActualValueMonoid)ˣ) := by
  constructor
  intro a b
  have key : ∀ u : (SourceHaarActualValueMonoid)ˣ,
      (u : SourceHaarActualValueMonoid) = 1 := by
    intro u
    have hmul : ((u : SourceHaarActualValueMonoid) *
        ((u⁻¹ : (SourceHaarActualValueMonoid)ˣ) : SourceHaarActualValueMonoid)) = 1 :=
      Units.mul_inv u
    have hta : (((u : SourceHaarActualValueMonoid) *
        ((u⁻¹ : (SourceHaarActualValueMonoid)ˣ) :
          SourceHaarActualValueMonoid))).toAdd = 0 := by
      rw [hmul]
      rfl
    rw [toAdd_mul] at hta
    have hx : (((u : SourceHaarActualValueMonoid)).toAdd : ℝ) ≤ 0 :=
      ((u : SourceHaarActualValueMonoid)).toAdd.property
    have hy : ((((u⁻¹ : (SourceHaarActualValueMonoid)ˣ) :
        SourceHaarActualValueMonoid)).toAdd : ℝ) ≤ 0 :=
      (((u⁻¹ : (SourceHaarActualValueMonoid)ˣ) :
        SourceHaarActualValueMonoid)).toAdd.property
    have hsum : (((u : SourceHaarActualValueMonoid)).toAdd : ℝ) +
        ((((u⁻¹ : (SourceHaarActualValueMonoid)ˣ) :
          SourceHaarActualValueMonoid)).toAdd : ℝ) = 0 := by
      have h := congrArg (fun z : sourceHaarActualNonpositiveAddSubmonoid => (z : ℝ)) hta
      simpa using h
    have hzero : (((u : SourceHaarActualValueMonoid)).toAdd : ℝ) = 0 := by linarith
    have h0 : ((u : SourceHaarActualValueMonoid)).toAdd = 0 := Subtype.ext hzero
    calc (u : SourceHaarActualValueMonoid)
        = Multiplicative.ofAdd ((u : SourceHaarActualValueMonoid).toAdd) := rfl
      _ = Multiplicative.ofAdd 0 := by rw [h0]
      _ = 1 := rfl
  apply Units.ext
  exact (key a).trans (key b).symm

/-- The unit group of the reduced anchor at every place is trivial. -/
theorem reducedQPilotAnchor_units_subsingleton (D : S1895PaperInput)
    (v : PaperV) : Subsingleton ((reducedQPilotAnchor D).Mon v)ˣ := by
  change Subsingleton ((SourceHaarActualValueMonoid)ˣ)
  infer_instance

/-- The times-mu fiber of the reduced anchor's canonical lift is trivial at
every place. -/
theorem reducedQPilotTimesMu_subsingleton (D : S1895PaperInput)
    (v : PaperV) : Subsingleton ((reducedQPilotTimesMu D).timesMu v) := by
  change Subsingleton (TimesMuQuotient ((reducedQPilotAnchor D).Mon v)ˣ)
  constructor
  intro x y
  obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
  obtain ⟨w, rfl⟩ := TimesMuQuotient.quotientMap_surjective y
  haveI : Subsingleton ((reducedQPilotAnchor D).Mon v)ˣ :=
    reducedQPilotAnchor_units_subsingleton D v
  rw [Subsingleton.elim u w]

/-- **Every R6 candidate has trivial times-mu fibers.**  Since the reduced
anchor's times-mu fibers are trivial, any paper strip identified with the
reduced anchor (in the full-poly-isomorphism sense of R6) has subsingleton
times-mu fibers at every place.  This is a necessary condition on the missing
paper strip; the paper q-pilot's x-mu layer, which is q_v-determined, is not
of this form. -/
theorem r6Proper_forces_trivial_timesMu (D : S1895PaperInput)
    (paperStrip : SourceFTimesMuPrimeStrip PaperV)
    (h : R6Proper D paperStrip) (v : PaperV) :
    Subsingleton (paperStrip.timesMu v) := by
  obtain ⟨phi⟩ := h
  obtain ⟨psi, _⟩ :=
    SourceFTimesMuPrimeStripFullPolyIsomorphism.representative_exists phi
  haveI : Subsingleton ((reducedQPilotTimesMu D).timesMu v) :=
    reducedQPilotTimesMu_subsingleton D v
  constructor
  intro x y
  obtain ⟨x', rfl⟩ := (psi.isoTimesMu v).surjective x
  obtain ⟨y', rfl⟩ := (psi.isoTimesMu v).surjective y
  rw [Subsingleton.elim x' y']

/-! ## 4. The tree's strips are q_v-blind -/

/-- Change only the initial theta data of the S1527 shear input, keeping the
actual Hodge-theater family (and the index equivalence) fixed. -/
noncomputable def withInitial (D : S1895PaperInput)
    (S : SourceDefinition31Data.{0} D.l)
    (h : S.arithmetic = (paperInput D).initial.arithmetic) :
    OriginalInput.{0, 0, 0, 0, 0} D.l PaperV where
  initial := S
  family := (paperInput D).family
  index_equiv := (paperInput D).index_equiv
  arithmetic_alignment := fun i => ((paperInput D).arithmetic_alignment i).trans h.symm

/-- Changing the initial theta data leaves every Hodge-theater strip unchanged:
the F-prime-strip only depends on the theater family and the index. -/
theorem fPrimeStripAt_withInitial (D : S1895PaperInput)
    (S : SourceDefinition31Data.{0} D.l)
    (h : S.arithmetic = (paperInput D).initial.arithmetic) (n m : Int) :
    (withInitial D S h).fPrimeStripAt n m = (paperInput D).fPrimeStripAt n m := rfl

/-- Concrete witness of q_v-blindness: the faithful one-place and the
two-place S1487 inputs have the same (1,0) F-prime-strip (the S1487 shear
strip) although their bad q_v families differ. -/
theorem candidate_blind (l : PrimeGeFive) :
    (S1487FaithfulInput (l := l)).fPrimeStripAt 1 0 =
      (S1487TwoPlaceInput (l := l)).fPrimeStripAt 1 0 := rfl

/-- The canonical times-mu lift of both inputs is the same as well. -/
theorem candidate_blind_timesMu (l : PrimeGeFive) :
    SourceFTimesMuPrimeStrip.canonical
        ((S1487FaithfulInput (l := l)).fPrimeStripAt 1 0) =
      SourceFTimesMuPrimeStrip.canonical
        ((S1487TwoPlaceInput (l := l)).fPrimeStripAt 1 0) := rfl

/-- The q-pilot log-volumes of the two inputs differ (-L vs -2L with
L = localLogMagnitude S1487Cand > 0).  Hence the strip does not determine the
q-pilot object, and it cannot be certified q_v-determined. -/
theorem qPilot_scalar_differs (l : PrimeGeFive) :
    sourceQPilotSignedLog (S1487FaithfulInput (l := l)).initial ≠
      sourceQPilotSignedLog (S1487TwoPlaceInput (l := l)).initial := by
  intro h
  have h' : -sourceBadQAbsLog (S1487FaithfulSourceData (l := l)) =
      -sourceBadQAbsLog (S1487TwoPlaceSourceData (l := l)) := h
  have hf : sourceBadQAbsLog (S1487FaithfulSourceData (l := l)) =
      sourceBadQAbsLog (S1487TwoPlaceSourceData (l := l)) := by
    simpa using congrArg Neg.neg h'
  rw [S1487Faithful_sourceBadQAbsLog, S1487TwoPlace_sourceBadQAbsLog] at hf
  have hpos := S1487Cand_magnitude_pos
  linarith

/-- **The available strips cannot be the q_v-determined paper strip**: there
are two S1527-type inputs with the same Hodge-theater family (hence the same
(1,0) strip and the same canonical times-mu lift) but different q-pilot
log-volumes.  The candidate canonical (I.fPrimeStripAt 1 0) is therefore
definitionally independent of the q_v data. -/
theorem availableStrip_not_qvDetermined (l : PrimeGeFive) :
    (∃ (I I' : OriginalInput.{0, 0, 0, 0, 0} l PaperV),
        I.family = I'.family ∧
        I.fPrimeStripAt 1 0 = I'.fPrimeStripAt 1 0 ∧
        sourceQPilotSignedLog I.initial ≠ sourceQPilotSignedLog I'.initial) := by
  refine ⟨S1487FaithfulInput (l := l), S1487TwoPlaceInput (l := l),
    rfl, rfl, ?_⟩
  exact qPilot_scalar_differs l

/-! ## 5. The exact first missing

R6 proper needs a *definition*:

  paperQPilotFTimesMuStrip D : SourceFTimesMuPrimeStrip PaperV

together with the identification of its associated pilot object (IUT II,
Definition 4.9, (viii)) with the actual q-pilot object constructed in section 1
(paperQPilotDivisor D, QVDeterminedQPilotObject D).  Neither the strip nor the
associated-pilot-object map exists in the tree, and the strip type
SourceFTimesMuPrimeStrip has no field referring to the global realified
Frobenioid or to arithmetic divisors.  Accordingly this file does not declare
such a definition, a paper-side type, or any inhabitant of
QPilotAnchorIdentification D P for a paper strip P; the reduction theorem below
is the exact interface that the missing definition must feed. -/

/-- The exact reduction that the missing definition of the paper strip has to
feed: once a paper-side q_v-determined times-mu strip P is supplied, R6 proper
is exactly the nonemptiness of the times-mu equivalence class from the reduced
anchor to P.  The paper side P is the missing definition. -/
theorem s1968_r6_exact_reduction (D : S1895PaperInput)
    (paperQPilotFTimesMuStrip : SourceFTimesMuPrimeStrip PaperV) :
    R6Proper D paperQPilotFTimesMuStrip ↔
      Nonempty (SourceFTimesMuPrimeStripEquivalence
        (reducedQPilotTimesMu D) paperQPilotFTimesMuStrip) :=
  r6Proper_iff D paperQPilotFTimesMuStrip

/-- The candidate closure P = reducedQPilotTimesMu D is the reduced
self-identification; it is not R6 proper (the paper side is not a paper
q-pilot strip, and by section 3 its times-mu fibers are trivial). -/
theorem s1968_candidate_closure_is_reducedSelf (D : S1895PaperInput) :
    R6Proper D (reducedQPilotTimesMu D) :=
  r6Proper_reducedSelf D

/-- The candidate canonical (I.fPrimeStripAt 1 0) is definitionally the reduced
anchor's canonical times-mu lift. -/
theorem candidate_eq_reducedQPilotTimesMu (D : S1895PaperInput) :
    SourceFTimesMuPrimeStrip.canonical ((paperInput D).fPrimeStripAt 1 0) =
      reducedQPilotTimesMu D := rfl

/-- **Status of R6 proper.**  The actual q-pilot object is constructed (section
1, QVDeterminedQPilotObject), and R6 reduces to the times-mu equivalence class
(section 5).  What is missing is the definition of the paper-side
q_v-determined times-mu strip and of its associated-pilot-object
identification; this file records that reduction together with the two
obstructions of sections 3/4 and does not fake the strip. -/
theorem s1968_status (D : S1895PaperInput) :
    Nonempty (QVDeterminedQPilotObject D) ∧
      (∀ (P : SourceFTimesMuPrimeStrip PaperV),
        R6Proper D P ↔
          Nonempty (SourceFTimesMuPrimeStripEquivalence
            (reducedQPilotTimesMu D) P)) ∧
      (∀ (P : SourceFTimesMuPrimeStrip PaperV),
        R6Proper D P → ∀ v : PaperV, Subsingleton (P.timesMu v)) :=
  ⟨qvDeterminedQPilotObject_exists D,
    fun P => r6Proper_iff D P,
    fun P h v => r6Proper_forces_trivial_timesMu D P h v⟩

/-! ## 6. Axiom probes -/

#print axioms paperQV
#print axioms paperQVOrder_abs_log
#print axioms paperQPilotDivisor
#print axioms paperQPilotDivisor_deg_eq_source
#print axioms paperQPilotDivisor_deg_pos
#print axioms paperQPilotLogVolume_eq_neg_deg
#print axioms paperQPilotLogVolume_neg
#print axioms qvDeterminedQPilotObject
#print axioms qvDeterminedQPilotObject_exists
#print axioms r6Proper_iff
#print axioms r6Proper_of_equivalence
#print axioms reducedQPilotTimesMu_subsingleton
#print axioms r6Proper_forces_trivial_timesMu
#print axioms fPrimeStripAt_withInitial
#print axioms candidate_blind
#print axioms qPilot_scalar_differs
#print axioms availableStrip_not_qvDetermined
#print axioms s1968_r6_exact_reduction
#print axioms s1968_status

end LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
