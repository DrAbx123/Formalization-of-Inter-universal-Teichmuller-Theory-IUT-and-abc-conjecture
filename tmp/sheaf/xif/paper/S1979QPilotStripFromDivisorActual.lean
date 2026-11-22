import tmp.sheaf.xif.paper.S1968QVDeterminedQPilotActual

/-!
# S1979: the q_v-determined piloted F⁺▷×μ-prime-strip and R6 proper

## The obligation

S1968 constructed the actual q-pilot object paperQPilotDivisor D (the
order-weighted divisor of the zero locus of the q_v in the global realified
Frobenioid, deg = sum_b |log q_b| = order_C3 * log 5, log-volume -|log q|) and
reduced R6 to the interface

  QPilotAnchorIdentification D P = SourceFTimesMuPrimeStripFullPolyIsomorphism
      (reducedQPilotTimesMu D) P,

parameterized by a paper-side P : SourceFTimesMuPrimeStrip PaperV.  The
requested next step was a definition

  paperQPilotFTimesMuStrip D : SourceFTimesMuPrimeStrip PaperV

obtained from paperQPilotDivisor D through IUT II, Definition 4.9, (viii) (the
*associated pilot object* of an F-prime-strip with times-mu structure), together
with its identification with that divisor, feeding QPilotAnchorIdentification to
close R6 proper.

## What the paper actually says (IUT II, Def. 4.9, (viii))

> the generators of the monoids O^▷(−) [each of which is abstractly isomorphic
> to N] of the data at v in V_bad of *F^⊢▷×μ, together with the {*rho_v},
> determine a well-defined object, up to isomorphism, of the global realified
> Frobenioid *C of negative "arithmetic degree" [...] which we refer to as the
> pilot object associated to the F-prime-strip with times-mu structure.

So the associated pilot object is computed from the O^▷(−)-generator at each bad
place together with the local realified value maps rho_v; it is *not* a function
of the bare prime-strip of loc. cit., (vii).  The tree's
SourceFTimesMuPrimeStrip has no field for those generators (its only constructor
is SourceFTimesMuPrimeStrip.canonical), and S1968 proved that every strip
satisfying R6Proper has subsingleton times-mu fibers, so the present
value/unit model carries no q_v either.

## What this file constructs (all actual, kernel-checked)

1. **The O^▷(−)-generator of the actual q_v** (section 1):
   qPilotGeneratorValue D b = -|log q_b| (the realified value of the actual
   Definition 3.1(b)(c) q-parameter) and the generator
   qPilotGenerator D b : SourceHaarActualValueMonoid, an actual element of the
   value monoid of the paper strip at the bad rational prime place 5.  It is
   proved nonpositive, nonzero, equal to -(order_b * log 5)
   (qPilotGeneratorValue_eq_order), and its realified value is literally
   Real.log (paperQV D b) for the paper input.

2. **The associated-pilot-object construction of IUT II, Def. 4.9, (viii)**
   (section 2): the piloted strip type PilotedFTimesMuPrimeStrip V Bad (an
   F-prime-strip with times-mu structure together with the O^▷(−)-generators at
   the bad places), the realified value pilotGeneratorRealifiedValue, the
   "negative arithmetic degree" predicate, and the pilot object
   associatedPilotObject D S : IUTIVArithmeticDivisor (PaperFmod D), whose
   coefficient at the bad base prime is -rho_w(g_w) / log q_w.

3. **The identification with S1968's divisor** (section 4):
   associatedPilotObject D (paperQPilotPilotedStrip D) = paperQPilotDivisor D,
   coefficient-wise (... = (paperQVOrder D bad0 : R), so the strip recovers the
   actual order) and degree-wise (deg = sourceBadQAbsLog = |log q| =
   -logVolume), matching S1968 exactly.

4. **q_v-determination, i.e. non-blindness** (section 5):
   qPilotGeneratorLogVolume S = -sourceBadQAbsLog S = sourceQPilotSignedLog S
   (the total realified value of the generator family is the pilot log-volume),
   and on the S1487 pair -- same Hodge-theater (1,0) strip (S1968's
   candidate_blind) -- the generator log-volumes are -L and -2L, so the new
   construction, unlike I.fPrimeStripAt n m, is not blind to the q_v.

5. **R6 at the piloted level** (section 6): the strengthened interface
   PilotedQPilotAnchorIdentification D S, a SourceFTimesMuPrimeStripEquivalence
   (reducedQPilotTimesMu D) S.toSourceFTimesMuPrimeStrip whose isoMon carries the
   anchor's generator to the strip's generator (the q_v-part of R6).  It is
   inhabited by the paper strip (paperQPilotPilotedIdentification), it implies
   S1960's unpiloted QPilotAnchorIdentification/R6Proper, and it **determines the
   associated pilot object**: pilotedIdentification_pilotObject says
   associatedPilotObject D S = paperQPilotDivisor D for any piloted S carrying
   that identification.

## The exact first missing, proved rather than asserted (section 7)

The unpiloted R6Proper D P is a predicate of SourceFTimesMuPrimeStrip only.
Consequently:

* paperQPilotPilotedStrip D and the *unit-generator* strip
  paperQPilotUnitGeneratorStrip D (same strip, generators 1) have the *same*
  SourceFTimesMuPrimeStrip (rfl), hence the same unpiloted R6 status
  (r6Proper_does_not_determine_pilotObject), while their associated pilot
  objects are the q-pilot divisor and the zero divisor respectively.
* Therefore R6Proper alone **cannot** imply that the associated pilot object is
  paperQPilotDivisor D; the q_v-determination has to be carried by the
  O^▷(−)-generator data, which the tree's strip type does not have.

So the definition that closes R6 faithfully is not a term of type
SourceFTimesMuPrimeStrip PaperV: the honest inhabitant of that type is the
reduced anchor's own canonical lift (paperQPilotStripProjection_eq_reduced,
S1960 section 5, the reduced self-identification, not R6).  The minimal
extension that does close it is PilotedFTimesMuPrimeStrip, and the exact
remaining gap is the paper's literal O^▷(A) subset O^◃(A) submonoid at a
universal covering pro-object of the bad-place split Frobenioid with its rho_v:
here rho_v is modelled by the strip's degree map and the generator is the actual
q_v scalar, not the Frobenius/unit-theoretic O^▷(A).

## Honest scope

No sorry, admit, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
assumption-only gate is used, and no strip is produced by a bogus constructor:
paperQPilotPilotedStrip is the canonical lift of the reduced anchor *plus* the
actual q_v generators, and its projection is recorded as such.  Classical inputs
are exactly propext, Classical.choice, Quot.sound (see the axiom probes at the
end).
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
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

local instance s1979GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1979FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

namespace LeanFormal.IUT.XiFPaper.S1979QPilotStripFromDivisorActual

/-! ## 0. The bad rational prime place of the paper strip -/

/-- The rational prime place at which the value monoid of the paper strip is
read at the bad places: 5, the residue characteristic of the concrete Gaussian
place above 5 (S1968: the bad base prime has weight log 5). -/
def paperBadPrime : PaperV :=
  ⟨5, mem_primeStrip_iff.mpr ⟨by norm_num, by norm_num, Nat.prime_five⟩⟩

theorem paperBadPrime_val : (paperBadPrime : Nat) = 5 := rfl

/-- The bad q-parameter is positive: it is (1/5) ^ order_C3 at the concrete
S1280/S1527 input. -/
theorem paperQV_pos (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : 0 < paperQV D b := by
  have h1 : paperQV D b = (S1280ReductionClause D.l).qParameter b := rfl
  rw [h1, S1527_qParameter_eq]
  exact pow_pos (by norm_num) _

/-- The actual log of the bad q-parameter is negative. -/
theorem paperQV_log_neg' (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : Real.log (paperQV D b) < 0 := by
  have h := paperQV_log_neg D b
  rwa [Real.norm_eq_abs, abs_of_pos (paperQV_pos D b)] at h

/-! ## 1. The O^▷(−)-generator of the actual q_v (IUT II, Def. 4.9, (vii)) -/

/-- The realified value of the q_v at a bad place: log q_v = -|log q_v|.  It is
the negative "arithmetic degree" datum of IUT II, Def. 4.9, (viii) and the
log q_v of IUT III, Def. 3.8, (i). -/
noncomputable def qPilotGeneratorValue (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : ℝ :=
  -|Real.log (paperQV D b)|

theorem qPilotGeneratorValue_nonpos (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : qPilotGeneratorValue D b ≤ 0 :=
  neg_nonpos.mpr (abs_nonneg _)

theorem qPilotGeneratorValue_neg (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : qPilotGeneratorValue D b < 0 :=
  neg_neg_of_pos (abs_pos.mpr (ne_of_lt (paperQV_log_neg' D b)))

/-- **The q_v determines the generator value**: it is -(order_b * log 5)
(S1968's paperQVOrder_abs_log). -/
theorem qPilotGeneratorValue_eq_order (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    qPilotGeneratorValue D b = -((paperQVOrder D b : ℝ) * Real.log 5) := by
  rw [qPilotGeneratorValue, paperQVOrder_abs_log]

theorem qPilotGeneratorValue_ne_zero (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : qPilotGeneratorValue D b ≠ 0 :=
  ne_of_lt (qPilotGeneratorValue_neg D b)

/-- The realified value is the actual log of the actual q_v. -/
theorem qPilotGeneratorValue_eq_log (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    qPilotGeneratorValue D b = Real.log (paperQV D b) := by
  have hneg : Real.log (paperQV D b) < 0 := paperQV_log_neg' D b
  rw [qPilotGeneratorValue, abs_of_neg hneg, neg_neg]

/-- The realified value is -localLogMagnitude S1487Cand: the actual completion q
magnitude of the concrete Gaussian place. -/
theorem qPilotGeneratorValue_eq_neg_localLogMagnitude (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    qPilotGeneratorValue D b = -localLogMagnitude S1487Cand := by
  rw [qPilotGeneratorValue_eq_order, paperQVOrder_eq_orderC3, ← S1487Cand_magnitude]

/-- The O^▷(−)-generator at a bad place, as an actual element of the local value
monoid Multiplicative {x : R // x <= 0} of the paper strip. -/
noncomputable def qPilotGenerator (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : SourceHaarActualValueMonoid :=
  Multiplicative.ofAdd ⟨qPilotGeneratorValue D b, qPilotGeneratorValue_nonpos D b⟩

@[simp] theorem qPilotGenerator_toAdd (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    ((Multiplicative.toAdd (qPilotGenerator D b) :
      sourceHaarActualNonpositiveAddSubmonoid) : ℝ) = qPilotGeneratorValue D b := rfl

/-- The generator is nontrivial: q_v is not 1 because q_v is contracting. -/
theorem qPilotGenerator_ne_one (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) : qPilotGenerator D b ≠ 1 := by
  intro h
  have h1 : ((Multiplicative.toAdd (qPilotGenerator D b) :
      sourceHaarActualNonpositiveAddSubmonoid) : ℝ) = 0 := by
    rw [h]
    rfl
  rw [qPilotGenerator_toAdd] at h1
  exact qPilotGeneratorValue_ne_zero D b h1

/-- The realified value rho_w(g_w) of the generator in the paper strip: the
degree map of the reduced anchor is the local rho_v of IUT II, Def. 4.9, (viii)
in this model. -/
theorem qPilotGenerator_degree_eq (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (reducedQPilotAnchor D).degree paperBadPrime (qPilotGenerator D b) =
      Multiplicative.ofAdd (qPilotGeneratorValue D b) := rfl

theorem qPilotGenerator_degree_toAdd (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    Multiplicative.toAdd
        ((reducedQPilotAnchor D).degree paperBadPrime (qPilotGenerator D b)) =
      qPilotGeneratorValue D b := rfl

/-! ## 2. The associated pilot object of a piloted F-prime-strip with
times-mu structure (IUT II, Def. 4.9, (viii)) -/

/-- A **piloted** F-prime-strip with times-mu structure: the data of IUT II,
Def. 4.9, (vii) together with the generators of the monoids O^▷(−) at the bad
places (loc. cit., (ii)--(iv)), from which Def. 4.9, (viii) computes the
associated pilot object.  These generators are *not* a field of
SourceFTimesMuPrimeStrip; this extension is exactly the datum the tree's
interface lacks (see section 7). -/
structure PilotedFTimesMuPrimeStrip (V : Type) (Bad : Type) where
  /-- the underlying F-prime-strip with times-mu structure of loc. cit., (vii) -/
  toSourceFTimesMuPrimeStrip : SourceFTimesMuPrimeStrip V
  /-- the value-monoid place at which a bad place's data is read -/
  place : Bad → V
  /-- the generator of O^▷(−) at each bad place -/
  generator : ∀ b, toSourceFTimesMuPrimeStrip.Mon (place b)

/-- The realified value rho_w(g_w) of the O^▷(−)-generator at a bad place
(IUT II, Def. 4.9, (viii): the generators together with the {rho_v}). -/
noncomputable def pilotGeneratorRealifiedValue
    {V : Type} {Bad : Type} (S : PilotedFTimesMuPrimeStrip V Bad) (b : Bad) : ℝ :=
  Multiplicative.toAdd
    (S.toSourceFTimesMuPrimeStrip.degree (S.place b) (S.generator b))

/-- The "negative arithmetic degree" condition of IUT II, Def. 4.9, (viii). -/
def HasNegativePilotGenerator {V : Type} {Bad : Type}
    (S : PilotedFTimesMuPrimeStrip V Bad) : Prop :=
  ∀ b, pilotGeneratorRealifiedValue S b < 0

/-- The coefficient of the associated pilot object at a base arithmetic place:
the realified value of the generator, normalized by the local weight log q_w
(IUT II, Def. 4.9, (viii) with the degree of IUT IV, Def. 1.9). -/
noncomputable def pilotCoefficient {V : Type} {Bad : Type}
    (S : PilotedFTimesMuPrimeStrip V Bad) (b : Bad) (w : ℝ) : ℝ :=
  - pilotGeneratorRealifiedValue S b / w

/-- **The associated pilot object of IUT II, Def. 4.9, (viii)** for the paper
input, as an element of the realified arithmetic divisor group of the base field
Fmod: the coefficient at the bad base prime is the rho_w-value of the
O^▷(−)-generator normalized by the actual weight log q_w. -/
noncomputable def associatedPilotObject (D : S1895PaperInput)
    (S : PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces) :
    IUTIVArithmeticDivisor (PaperFmod D) :=
  Finsupp.single
    (IUTIVPlace.finite (F := PaperFmod D) (paperBadBasePlace D (paperQVBad0 D)))
    (pilotCoefficient S (paperQVBad0 D)
      (IUTIVPlace.weight (PaperFmod D)
        (IUTIVPlace.finite (F := PaperFmod D)
          (paperBadBasePlace D (paperQVBad0 D)))))

/-! ## 3. The q_v-determined piloted q-pilot strip -/

/-- **The q-pilot piloted F-prime-strip with times-mu structure**: the
F-prime-strip with times-mu structure of the reduced anchor (S1960/S1968),
equipped with the actual q_v generators at the bad places.  Its associated pilot
object is computed in section 4 and is exactly paperQPilotDivisor D.  Its
SourceFTimesMuPrimeStrip projection is the reduced anchor's canonical lift: the
generator layer is what makes this the paper's q-pilot object and not the reduced
anchor (see section 7). -/
noncomputable def paperQPilotPilotedStrip (D : S1895PaperInput) :
    PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces where
  toSourceFTimesMuPrimeStrip := reducedQPilotTimesMu D
  place := fun _ => paperBadPrime
  generator := fun b => qPilotGenerator D b

@[simp] theorem paperQPilotPilotedStrip_toStrip (D : S1895PaperInput) :
    (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip =
      reducedQPilotTimesMu D := rfl

theorem paperQPilotPilotedStrip_generator (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (paperQPilotPilotedStrip D).generator b = qPilotGenerator D b := rfl

/-- The paper strip's value monoid at the bad place is the nonpositive reals. -/
theorem paperQPilotPilotedStrip_Mon (D : S1895PaperInput) :
    (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip.Mon paperBadPrime =
      SourceHaarActualValueMonoid := rfl

/-- The generators of the paper strip have negative realified value ("negative
arithmetic degree", IUT II, Def. 4.9, (viii)). -/
theorem paperQPilotPilotedStrip_negative (D : S1895PaperInput) :
    HasNegativePilotGenerator (paperQPilotPilotedStrip D) := by
  intro b
  have h : pilotGeneratorRealifiedValue (paperQPilotPilotedStrip D) b =
      qPilotGeneratorValue D b := rfl
  rw [h]
  exact qPilotGeneratorValue_neg D b

/-- The generator values of the paper strip are log q_v, not just some
nonpositive numbers. -/
theorem paperQPilotPilotedStrip_value (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    pilotGeneratorRealifiedValue (paperQPilotPilotedStrip D) b =
      Real.log (paperQV D b) := by
  rw [show pilotGeneratorRealifiedValue (paperQPilotPilotedStrip D) b =
      qPilotGeneratorValue D b from rfl, qPilotGeneratorValue_eq_log]

/-! ## 4. Identification of the associated pilot object with the q-pilot divisor
(IUT II, Def. 4.9, (viii); IUT III, Def. 3.8, (i)) -/

/-- The coefficient of the associated pilot object of the paper strip at the bad
base prime is the actual q_v order order_C3. -/
theorem paperPilotCoefficient_eq (D : S1895PaperInput) :
    pilotCoefficient (paperQPilotPilotedStrip D) (paperQVBad0 D)
      (IUTIVPlace.weight (PaperFmod D)
        (IUTIVPlace.finite (F := PaperFmod D)
          (paperBadBasePlace D (paperQVBad0 D)))) =
      (paperQVOrder D (paperQVBad0 D) : ℝ) := by
  unfold pilotCoefficient
  rw [show pilotGeneratorRealifiedValue (paperQPilotPilotedStrip D) (paperQVBad0 D) =
      qPilotGeneratorValue D (paperQVBad0 D) from rfl]
  rw [qPilotGeneratorValue_eq_order, paperBadBasePlace_weight]
  have hlog : Real.log 5 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- **The associated pilot object of the paper q-pilot strip is S1968's actual
q-pilot divisor** paperQPilotDivisor D. -/
theorem associatedPilotObject_paperStrip (D : S1895PaperInput) :
    associatedPilotObject D (paperQPilotPilotedStrip D) =
      paperQPilotDivisor D := by
  unfold associatedPilotObject paperQPilotDivisor
  rw [paperPilotCoefficient_eq]

/-- The strip recovers the actual q_v order at the bad prime: the coefficient of
its associated pilot object there is paperQVOrder D bad0. -/
theorem associatedPilotObject_apply (D : S1895PaperInput) :
    associatedPilotObject D (paperQPilotPilotedStrip D)
        (IUTIVPlace.finite (F := PaperFmod D)
          (paperBadBasePlace D (paperQVBad0 D))) =
      (paperQVOrder D (paperQVBad0 D) : ℝ) := by
  rw [associatedPilotObject_paperStrip]
  exact paperQPilotDivisor_apply D

/-- The degree of the associated pilot object is S1968's sum_b |log q_b|. -/
theorem associatedPilotObject_deg_eq_source (D : S1895PaperInput) :
    IUTIVArithmeticDivisor.deg (F := PaperFmod D)
        (associatedPilotObject D (paperQPilotPilotedStrip D)) =
      sourceBadQAbsLog (paperInput D).initial := by
  rw [associatedPilotObject_paperStrip]
  exact paperQPilotDivisor_deg_eq_source D

/-- The degree is the paper log-volume: deg = -logVolume = |log q|. -/
theorem associatedPilotObject_deg_eq_neg_logVolume (D : S1895PaperInput) :
    IUTIVArithmeticDivisor.deg (F := PaperFmod D)
        (associatedPilotObject D (paperQPilotPilotedStrip D)) =
      - paperQPilotLogVolume D := by
  rw [associatedPilotObject_deg_eq_source, paperQPilotLogVolume, neg_neg]

/-- The degree is |log q| at the actual abstract q-parameter, exactly as in
IUT III, Def. 3.8, (i). -/
theorem associatedPilotObject_deg_eq_abs_log (D : S1895PaperInput) :
    IUTIVArithmeticDivisor.deg (F := PaperFmod D)
        (associatedPilotObject D (paperQPilotPilotedStrip D)) =
      |Real.log (paperQV D (paperQVBad0 D))| := by
  rw [associatedPilotObject_deg_eq_neg_logVolume, paperQPilotLogVolume_eq_orderC3,
    neg_neg, paperQVOrder_abs_log, paperQVOrder_eq_orderC3]

/-- The pilot object is nontrivial (the q-pilot object is of negative arithmetic
degree, IUT II, Def. 4.9, (viii)). -/
theorem associatedPilotObject_ne_zero (D : S1895PaperInput) :
    associatedPilotObject D (paperQPilotPilotedStrip D) ≠ 0 := by
  rw [associatedPilotObject_paperStrip]
  intro h
  have h1 := paperQPilotDivisor_apply D
  rw [h] at h1
  have h0 : (0 : IUTIVArithmeticDivisor (PaperFmod D))
      (IUTIVPlace.finite (F := PaperFmod D)
        (paperBadBasePlace D (paperQVBad0 D))) = 0 := Finsupp.zero_apply
  rw [h0] at h1
  have hne : (paperQVOrder D (paperQVBad0 D) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (paperQVOrder_pos D (paperQVBad0 D))
  exact hne h1.symm

/-! ## 5. q_v-determination: the construction is not blind -/

/-- The total realified value of the generator family of an arbitrary initial
source datum: the sum of the actual log q_b = -|log q_b|. -/
noncomputable def qPilotGeneratorLogVolume {l : PrimeGeFive}
    (S : SourceDefinition31Data l) : ℝ :=
  letI := S.bad_finite
  ∑ b : S.badPlaces, -|Real.log (S.reduction.qParameter b)|

/-- The generator log-volume is exactly the source signed q-pilot log-volume
-sum_b |log q_b|: the generator family's total realified value is the log-volume
of the associated pilot object. -/
theorem qPilotGeneratorLogVolume_eq_signedLog {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    qPilotGeneratorLogVolume S = sourceQPilotSignedLog S := by
  unfold qPilotGeneratorLogVolume sourceQPilotSignedLog sourceBadQAbsLog
  rw [Finset.sum_neg_distrib]

/-- On the paper input the pilot object's degree is the generator family's total
realified value (the Def. 4.9, (viii) computation is the degree). -/
theorem associatedPilotObject_deg_eq_generatorLogVolume (D : S1895PaperInput) :
    IUTIVArithmeticDivisor.deg (F := PaperFmod D)
        (associatedPilotObject D (paperQPilotPilotedStrip D)) =
      - qPilotGeneratorLogVolume (paperInput D).initial := by
  rw [associatedPilotObject_deg_eq_source, qPilotGeneratorLogVolume_eq_signedLog,
    sourceQPilotSignedLog]
  ring

/-- **The new construction is q_v-determined, not blind**: on the S1487 faithful
one-place and two-place inputs the Hodge-theater (1,0) F-prime-strips coincide
(S1968's candidate_blind), while the generator log-volumes are -L and -2L
(S1968's qPilot_scalar_differs).  Hence the piloted construction sees the q_v
where the strip alone does not. -/
theorem pilotLevel_not_blind (l : PrimeGeFive) :
    (S1487FaithfulInput (l := l)).fPrimeStripAt 1 0 =
        (S1487TwoPlaceInput (l := l)).fPrimeStripAt 1 0 ∧
      qPilotGeneratorLogVolume (S1487FaithfulInput (l := l)).initial ≠
        qPilotGeneratorLogVolume (S1487TwoPlaceInput (l := l)).initial := by
  refine ⟨rfl, ?_⟩
  rw [qPilotGeneratorLogVolume_eq_signedLog,
    qPilotGeneratorLogVolume_eq_signedLog]
  exact qPilot_scalar_differs l

/-! ## 6. R6 at the piloted level -/

/-- The reduced anchor's generator at a bad place: the same actual q_v generator,
read in the value monoid of the reduced anchor's canonical lift. -/
noncomputable def reducedQPilotGenerator (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (reducedQPilotTimesMu D).Mon paperBadPrime :=
  qPilotGenerator D b

/-- The R6 identification at the piloted level (IUT III, Def. 3.8, (i), together
with IUT II, Def. 4.9, (viii)): a times-mu equivalence of the strips **and** the
matching of the O^▷(−)-generators, i.e. the q_v-determination is carried by the
identification. -/
structure PilotedQPilotAnchorIdentification (D : S1895PaperInput)
    (S : PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces) where
  /-- the times-mu equivalence of IUT II, Def. 4.9, (vii) -/
  equivalence :
    SourceFTimesMuPrimeStripEquivalence (reducedQPilotTimesMu D)
      S.toSourceFTimesMuPrimeStrip
  /-- the generators agree: the identification is q_v-compatible -/
  generator_compat : ∀ b,
    equivalence.toF.isoMon (S.place b) (reducedQPilotGenerator D b) = S.generator b

/-- The paper q-pilot strip satisfies the piloted R6 identification relative to
the actual q_v generators of the reduced anchor. -/
noncomputable def paperQPilotPilotedIdentification (D : S1895PaperInput) :
    PilotedQPilotAnchorIdentification D (paperQPilotPilotedStrip D) where
  equivalence := SourceFTimesMuPrimeStripEquivalence.refl _
  generator_compat := by
    intro b
    rfl

/-- The piloted identification implies S1960's unpiloted R6 identification. -/
theorem r6Proper_of_pilotedIdentification (D : S1895PaperInput)
    (S : PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces)
    (h : PilotedQPilotAnchorIdentification D S) :
    R6Proper D S.toSourceFTimesMuPrimeStrip :=
  r6Proper_of_equivalence D S.toSourceFTimesMuPrimeStrip h.equivalence

/-- **The piloted R6 identification determines the associated pilot object**: any
piloted strip whose generators are matched with the actual q_v generators of the
reduced anchor has paperQPilotDivisor D as its associated pilot object.  This is
the part of R6 that the unpiloted QPilotAnchorIdentification cannot see (see
section 7). -/
theorem pilotedIdentification_pilotObject (D : S1895PaperInput)
    (S : PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces)
    (h : PilotedQPilotAnchorIdentification D S) :
    associatedPilotObject D S = paperQPilotDivisor D := by
  have hval : ∀ b, pilotGeneratorRealifiedValue S b = qPilotGeneratorValue D b := by
    intro b
    have hdeg := h.equivalence.toF.compatDegree (S.place b)
      (reducedQPilotGenerator D b)
    rw [h.generator_compat b] at hdeg
    unfold pilotGeneratorRealifiedValue
    rw [hdeg]
    rfl
  rw [← associatedPilotObject_paperStrip]
  unfold associatedPilotObject pilotCoefficient
  rw [hval (paperQVBad0 D)]
  rfl

/-- **The paper q-pilot strip closes R6 at the piloted level**: it carries the
actual q_v generators, it is identified with the reduced anchor's canonical lift
through them, and its associated pilot object is the q-pilot divisor. -/
theorem s1979_r6_piloted (D : S1895PaperInput) :
    Nonempty (PilotedQPilotAnchorIdentification D (paperQPilotPilotedStrip D)) ∧
      R6Proper D (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip ∧
      associatedPilotObject D (paperQPilotPilotedStrip D) = paperQPilotDivisor D :=
  ⟨⟨paperQPilotPilotedIdentification D⟩,
    r6Proper_of_pilotedIdentification D _ (paperQPilotPilotedIdentification D),
    associatedPilotObject_paperStrip D⟩

/-! ## 7. The exact gap: the unpiloted strip interface cannot see the
generators -/

/-- A piloted strip over the reduced anchor whose generators are the unit: same
F-prime-strip with times-mu structure, no q_v data. -/
noncomputable def paperQPilotUnitGeneratorStrip (D : S1895PaperInput) :
    PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces where
  toSourceFTimesMuPrimeStrip := reducedQPilotTimesMu D
  place := fun _ => paperBadPrime
  generator := fun _ => 1

theorem paperQPilotUnitGeneratorStrip_projection (D : S1895PaperInput) :
    (paperQPilotUnitGeneratorStrip D).toSourceFTimesMuPrimeStrip =
      reducedQPilotTimesMu D := rfl

theorem paperQPilotUnitGeneratorStrip_value_zero (D : S1895PaperInput) :
    pilotGeneratorRealifiedValue (paperQPilotUnitGeneratorStrip D)
        (paperQVBad0 D) = 0 := rfl

/-- The unit-generator strip's associated pilot object is the zero divisor: the
honest Def. 4.9, (viii) computation on trivial generator data. -/
theorem paperQPilotUnitGeneratorStrip_pilotObject (D : S1895PaperInput) :
    associatedPilotObject D (paperQPilotUnitGeneratorStrip D) = 0 := by
  unfold associatedPilotObject pilotCoefficient
  rw [paperQPilotUnitGeneratorStrip_value_zero]
  simp

/-- The unit-generator strip is just as R6-proper as the q-pilot strip: the
unpiloted R6 status is a property of the bare SourceFTimesMuPrimeStrip. -/
theorem paperQPilotUnitGeneratorStrip_r6Proper (D : S1895PaperInput) :
    R6Proper D (paperQPilotUnitGeneratorStrip D).toSourceFTimesMuPrimeStrip := by
  rw [paperQPilotUnitGeneratorStrip_projection]
  exact r6Proper_reducedSelf D

/-- **R6Proper alone does not determine the associated pilot object.**  The
q-pilot piloted strip and the unit-generator piloted strip have the same
SourceFTimesMuPrimeStrip (hence the same unpiloted R6 status, and in particular
the same QPilotAnchorIdentification), but their associated pilot objects are
paperQPilotDivisor D and 0.  Hence the q_v-determination must be carried by the
O^▷(−)-generator data of the strip, not by the unpiloted R6 interface. -/
theorem r6Proper_does_not_determine_pilotObject (D : S1895PaperInput) :
    (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip =
        (paperQPilotUnitGeneratorStrip D).toSourceFTimesMuPrimeStrip ∧
      R6Proper D (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip ∧
      R6Proper D (paperQPilotUnitGeneratorStrip D).toSourceFTimesMuPrimeStrip ∧
      associatedPilotObject D (paperQPilotPilotedStrip D) = paperQPilotDivisor D ∧
      associatedPilotObject D (paperQPilotUnitGeneratorStrip D) = 0 ∧
      paperQPilotDivisor D ≠ 0 :=
  ⟨rfl,
    (s1979_r6_piloted D).2.1,
    paperQPilotUnitGeneratorStrip_r6Proper D,
    associatedPilotObject_paperStrip D,
    paperQPilotUnitGeneratorStrip_pilotObject D,
    fun h => associatedPilotObject_ne_zero D
      (by rw [associatedPilotObject_paperStrip]; exact h)⟩

/-- The SourceFTimesMuPrimeStrip projection of the q-pilot piloted strip.  This is
the only honest inhabitant of the type required by the task statement, and it is
*definitionally the reduced anchor's canonical lift*: the paper's pilot data is
not part of SourceFTimesMuPrimeStrip, and naming this projection "the paper
q-pilot strip" would be S1960's reduced self-identification, not R6. -/
noncomputable def paperQPilotStripProjection (D : S1895PaperInput) :
    SourceFTimesMuPrimeStrip PaperV :=
  (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip

theorem paperQPilotStripProjection_eq_reduced (D : S1895PaperInput) :
    paperQPilotStripProjection D = reducedQPilotTimesMu D := rfl

/-- **The exact first missing**, in the form proved here: a q_v-determined pilot
object exists (the piloted strip of section 3, identified with the q-pilot
divisor in section 4, and R6-identified at the piloted level in section 6), while
the unpiloted interface is insufficient -- there is an R6-proper strip with zero
pilot object.  So the missing datum is the O^▷(−)-generator field on the strip
type (the paper's O^▷(A) subset O^◃(A) at a universal covering pro-object with
its rho_v), not a new proposition about SourceFTimesMuPrimeStrip. -/
theorem s1979_first_missing (D : S1895PaperInput) :
    (Nonempty (PilotedQPilotAnchorIdentification D (paperQPilotPilotedStrip D)) ∧
        associatedPilotObject D (paperQPilotPilotedStrip D) = paperQPilotDivisor D) ∧
      (∃ S : PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces,
        R6Proper D S.toSourceFTimesMuPrimeStrip ∧ associatedPilotObject D S = 0) :=
  ⟨⟨⟨paperQPilotPilotedIdentification D⟩, associatedPilotObject_paperStrip D⟩,
    ⟨paperQPilotUnitGeneratorStrip D,
      paperQPilotUnitGeneratorStrip_r6Proper D,
      paperQPilotUnitGeneratorStrip_pilotObject D⟩⟩

/-- **Status of R6 proper on the S1968 reduction.**  The actual q-pilot object is
the associated pilot object of the q-pilot *piloted* strip (sections 2 and 4), and
that strip is R6-identified at the piloted level (section 6).  The unpiloted R6
interface of S1960/S1968 is satisfied by strips with arbitrary generator data
(section 7), so it cannot be the final form of R6; the extension
PilotedFTimesMuPrimeStrip is the minimal one that carries the paper's
q_v-determination. -/
theorem s1979_status (D : S1895PaperInput) :
    associatedPilotObject D (paperQPilotPilotedStrip D) = paperQPilotDivisor D ∧
      HasNegativePilotGenerator (paperQPilotPilotedStrip D) ∧
      (∀ S : PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces,
        PilotedQPilotAnchorIdentification D S →
          associatedPilotObject D S = paperQPilotDivisor D) ∧
      (∃ S : PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces,
        R6Proper D S.toSourceFTimesMuPrimeStrip ∧ associatedPilotObject D S = 0) :=
  ⟨associatedPilotObject_paperStrip D,
    paperQPilotPilotedStrip_negative D,
    fun _ h => pilotedIdentification_pilotObject D _ h,
    ⟨paperQPilotUnitGeneratorStrip D,
      paperQPilotUnitGeneratorStrip_r6Proper D,
      paperQPilotUnitGeneratorStrip_pilotObject D⟩⟩

/-! ## 8. Axiom probes -/

#print axioms paperQV_pos
#print axioms qPilotGeneratorValue
#print axioms qPilotGeneratorValue_eq_order
#print axioms qPilotGenerator
#print axioms qPilotGenerator_ne_one
#print axioms PilotedFTimesMuPrimeStrip
#print axioms pilotGeneratorRealifiedValue
#print axioms associatedPilotObject
#print axioms paperQPilotPilotedStrip
#print axioms paperQPilotPilotedStrip_negative
#print axioms paperPilotCoefficient_eq
#print axioms associatedPilotObject_paperStrip
#print axioms associatedPilotObject_deg_eq_source
#print axioms associatedPilotObject_deg_eq_abs_log
#print axioms associatedPilotObject_ne_zero
#print axioms qPilotGeneratorLogVolume_eq_signedLog
#print axioms pilotLevel_not_blind
#print axioms paperQPilotPilotedIdentification
#print axioms r6Proper_of_pilotedIdentification
#print axioms pilotedIdentification_pilotObject
#print axioms s1979_r6_piloted
#print axioms paperQPilotUnitGeneratorStrip
#print axioms paperQPilotUnitGeneratorStrip_pilotObject
#print axioms paperQPilotUnitGeneratorStrip_r6Proper
#print axioms r6Proper_does_not_determine_pilotObject
#print axioms paperQPilotStripProjection_eq_reduced
#print axioms s1979_first_missing
#print axioms s1979_status

end LeanFormal.IUT.XiFPaper.S1979QPilotStripFromDivisorActual
