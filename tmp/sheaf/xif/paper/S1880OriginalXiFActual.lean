import tmp.sheaf.xif.paper.S1684ThetaLinkFromActualOActual
import tmp.sheaf.xif.paper.OrigXiFPaperSignedHullActual

/-!
# S1880: the original Theta-link xi-f -- the xi-f inequality itself, the
# paper-route Theta-link object on the actual S1679 O(-D) carrier, and the
# precise first missing object

Layer: **O** (original-text Theta-link / xi-f).  This file does **not** use the
N-layer PaperXiFFinalActual.paperLevelXiF_actual / ActualPaperXiFTarget: that
target is the normalized qVFam tensor/hull scalar over
SourceNativeInitialThetaData and is *not* the original Theta-link.  It also does
not use the native target (T), does not substitute the SourceDefinition31Data
contract for paper data, and does not use a D4-D9 assembly wrapper.

## Actual O/D objects read

* S1679CompleteODCarrierActual.s1679Carrier -- the paper arithmetic line-bundle
  carrier: total = the complete O(-D) submodule s1673Total, localizations =
  s1673Localization; not S1423Module, not a free lattice, not a completion
  carrier.
* S1680QPilotObjectActual.s1680QPilotObject -- the full frozen PaperQPilotObject
  with the S1679 carrier, sourceQPilotStrip, actualOneColumnFinitePrimePlace,
  OrigXiFPaperSourceKummerArrow and sourceQPilotSignedLog.
* S1684ThetaLinkFromActualOActual.s1684QPilotObject and
  s1684OrigXiFThetaLinkActual -- the same-shape object over the S1280 actual
  Gaussian assembled input, and the O-layer Theta-link structure, conditional
  exactly on the paper Definition 3.1 clause supply R.

## Status of what this file establishes

1. [PROVED] **The xi-f log-volume inequality itself.**  At the actual Q(i) place
   above 5, with the actual completion q, for **every** actual paper signed-hull
   datum D:
     -|log ||q||| <= -|log Theta|   (s1880_xiF_inequality_abs),
   strictly (s1880_xiF_inequality_strict), hence a membership in the paper ray
   R_{<= -|log Theta|} (s1880_xiF_ray).  No source contract, no R, no
   PUnit/True/toy input is used.
2. [PROVED] The paper-route object's q-pilot scalar is exactly the actual paper
   scalar -(order_C3 * log 5) (s1880_paper_qPilotLogVolume_eq), and it does
   **not** depend on the content of the clause supply R
   (s1880_qPilotLogVolume_independent_of_supply): R is only used to *form* the
   paper input and its C3, never to evaluate the xi-f scalar.
3. [BUILT] On the paper-route object S1880PaperO carrying the actual S1679
   O(-D) line bundle, given R:
     OrigXiFThetaLinkActual (S1880PaperO R) D (S1880PaperC3 R)
   (s1880_paper_thetaLink), its concrete link_identification
   (s1880_paper_linkIdentification), and the xi-f ray membership
   (s1880_paper_xiF_ray).
4. [MISSING] The precise first missing object of the paper-level chain: the
   paper's Definition 3.1 clause supply, whose **first field is the D5 torsion
   clause** SourceTorsionClause.{0,0,0} l (S1880FirstMissing,
   s1880_firstMissing_of_supply); and, for the paper signed hull, the single
   procession-normalization field of OrigXiFPaperSignedHullData
   (s1880_signedHullDatum_bridge).  Both are *input data about paper objects*;
   by 1 and 2 the xi-f content is already a theorem, so neither is an xi-f
   statement.

## Boundary kept explicit

The O object used below is the S1684 same-shape object.  Its four
paper_*_identification fields are the concrete source-level propositions of
S1680: the source strip anchor plus theta-q agreement, the S1679 complete O(-D)
carrier with injective localizations, the IUT II Definition 4.9(i)
invariant-image law plus degree preservation, and the bad-place absolute-log
scalar.  They are **not** the paper's F^boxplus-triangleright-x-mu-prime-strip
identification, not the full paper log-Kummer correspondence, and not the (1,0)
label binding; those remain separate obligations of the O object and are
independent of the two Theta-link scalar fields proved here and of the xi-f
inequality proved in section 1.

No PUnit, True, toy, sorry, axiom, Nonempty gate, or arbitrary inhabitant is
used anywhere in this file.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1880OriginalXiFActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1554SignedHullFromQActual
open LeanFormal.IUT.XiFPaper.S1679CompleteODCarrierActual
open LeanFormal.IUT.XiFPaper.S1684ThetaLinkFromActualOActual
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiF.OrigXiFPaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkIdentificationActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

universe uX

variable {l : PrimeGeFive}

/- The concrete Gaussian arithmetic carries its own local instances in the
files that construct it; they are local there, so the field structure of
GaussianField is restated here for the actual completion q. -/
local instance s1880GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1880FivePrime : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ## 1. The xi-f inequality at the actual Gaussian completion q

These statements are unconditional: no source contract, no clause supply R, no
D beyond an actual paper signed-hull datum.  The actual q is the completion q of
the S1487/S1391 candidate at the concrete Gaussian place above 5, whose local
log magnitude is order * log 5 with order >= 1. -/

/-- The actual completion q has norm below one (it is a legitimate contracting
Definition 3.1(b) q-parameter). -/
theorem s1880_qNorm_lt_one : ‖S1487Cand.q‖ < 1 :=
  qNorm_lt_one S1487Cand

/-- The actual completion q has positive norm. -/
theorem s1880_qNorm_pos : 0 < ‖S1487Cand.q‖ :=
  qNorm_pos S1487Cand

/-- The paper magnitude -|log q| of the actual completion q is the actual local
log magnitude order * log 5. -/
theorem s1880_abs_log_q_eq_magnitude :
    |Real.log ‖S1487Cand.q‖| = localLogMagnitude S1487Cand :=
  abs_localSignedLog S1487Cand

/-- log 5 > 1, hence -log 5 < -1. -/
theorem s1880_neg_log_five_lt_neg_one : -Real.log 5 < -1 :=
  S1554_neg_log_five_lt_neg_one

/-- The actual q-pilot scalar is at most -log 5. -/
theorem s1880_neg_magnitude_le_neg_log_five :
    -localLogMagnitude S1487Cand ≤ -Real.log 5 :=
  S1554_neg_localLogMagnitude_le_neg_log_five

/-- The actual q-pilot scalar is strictly below -1. -/
theorem s1880_neg_magnitude_lt_neg_one :
    -localLogMagnitude S1487Cand < -1 :=
  S1554_neg_localLogMagnitude_lt_neg_one

/-- The actual q-pilot scalar is at most -1. -/
theorem s1880_neg_magnitude_le_neg_one :
    -localLogMagnitude S1487Cand ≤ -1 :=
  s1880_neg_magnitude_lt_neg_one.le

/-- **The paper xi-f comparison** -|log q| <= -|log Theta| at the actual
completion q, for every actual paper signed-hull datum D, with no hypothesis on
D beyond its own actual construction. -/
theorem s1880_xiF_inequality {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    -localLogMagnitude S1487Cand ≤ OrigXiFSignedThetaHullLogVolume D :=
  (lt_of_lt_of_le s1880_neg_magnitude_lt_neg_one
    (OrigXiFSignedThetaHullLogVolume_ge_neg_one D)).le

/-- The same comparison written in the paper's own -|log| form. -/
theorem s1880_xiF_inequality_abs {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    -|Real.log ‖S1487Cand.q‖| ≤ OrigXiFSignedThetaHullLogVolume D := by
  rw [s1880_abs_log_q_eq_magnitude]
  exact s1880_xiF_inequality D

/-- The comparison is strict: the paper's -|log Theta| is at least -1, while
the actual -|log q| is strictly below -1. -/
theorem s1880_xiF_inequality_strict {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    -|Real.log ‖S1487Cand.q‖| < OrigXiFSignedThetaHullLogVolume D := by
  rw [s1880_abs_log_q_eq_magnitude]
  exact lt_of_lt_of_le s1880_neg_magnitude_lt_neg_one
    (OrigXiFSignedThetaHullLogVolume_ge_neg_one D)

/-- **The xi-f membership**: -|log q| lies in the paper ray R_{<= -|log Theta|}
of the actual signed theta hull. -/
theorem s1880_xiF_ray {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    -|Real.log ‖S1487Cand.q‖| ∈ OrigXiFThetaHullLogVolumeRay D :=
  (OrigXiFmem_thetaHullLogVolumeRay_iff D).mpr (s1880_xiF_inequality_abs D)

/-- The paper ray of the actual PaperSignedHull built from D contains -|log q|.
This is the conclusion type of the paper ThetaLinkActual consumer
link_implies_inclusion, obtained here with no link input. -/
theorem s1880_xiF_paperSignedHullRay {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    -|Real.log ‖S1487Cand.q‖| ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume :=
  (OrigXiFThetaLinkRay_iff_le D (-|Real.log ‖S1487Cand.q‖|)).mpr
    (s1880_xiF_inequality_abs D)

/-! ## 2. The paper-route q-pilot object on the actual S1679 O(-D) carrier -/

/-- The paper-route q-pilot object: the S1684 same-shape actual object over the
S1280 actual Gaussian assembled input, carrying the actual S1679 complete O(-D)
line-bundle carrier. -/
noncomputable def S1880PaperO (l : PrimeGeFive) (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (S1527Input l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (OrigXiFPaperSourceKummerGroup l) (OrigXiFPaperSourceStrip l) :=
  s1684QPilotObject (l := l) R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

/-- The actual S1391 L-carrier C3 of the paper route, at the concrete Gaussian
place above 5. -/
noncomputable abbrev S1880PaperC3 (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    SourcePilotRegionDataL
      (I := S1527Input l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-- The paper-route object's q-pilot log-volume is the actual completion scalar
-localLogMagnitude S1487Cand = -(order_C3 * log 5), i.e. the paper's -|log q|
for q = 5 ^ (-order_C3). -/
theorem s1880_paper_qPilotLogVolume_eq (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1880PaperO l R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume =
      -localLogMagnitude S1487Cand := by
  unfold S1880PaperO
  rw [(s1684QPilotObject (l := l) R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume_eq]
  unfold sourceQPilotSignedLog
  rw [S1527Input_initial, S1527_sourceBadQAbsLog_eq_localLogMagnitude]

/-- The same scalar in the paper's -|log| form. -/
theorem s1880_paper_qPilotLogVolume_eq_neg_abs (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1880PaperO l R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume =
      -|Real.log ‖S1487Cand.q‖| := by
  rw [s1880_paper_qPilotLogVolume_eq, s1880_abs_log_q_eq_magnitude]

/-- The paper-route object's q-pilot log-volume evaluated numerically:
-(order_C3 * log 5), i.e. the paper -|log q| for q = 5 ^ (-order_C3). -/
theorem s1880_paper_qPilotLogVolume_eq_neg_order_mul_log_five (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1880PaperO l R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume =
      -((S1487Cand.order : ℝ) * Real.log 5) := by
  rw [s1880_paper_qPilotLogVolume_eq, S1487Cand_magnitude]

/-- **Paper xi-f on the actual paper-route object**: its q-pilot log-volume is
below the actual signed theta hull log-volume for every actual D, and no
clause-supply content is used. -/
theorem s1880_paper_qPilot_le_signedHull (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    (S1880PaperO l R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume ≤
      OrigXiFSignedThetaHullLogVolume D := by
  rw [s1880_paper_qPilotLogVolume_eq]
  exact s1880_xiF_inequality D

/-- **The xi-f scalar does not depend on the paper clause supply.**  For any two
supplies R, R' (and any D9 compatibility pairs) the paper-route objects have
exactly the same q-pilot log-volume.  Hence the missing clause supply is a
source-object input, not an xi-f quantity. -/
theorem s1880_qPilotLogVolume_independent_of_supply (l : PrimeGeFive)
    (R R' : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (redCompat' : Prop) (hredCompat' : redCompat')
    (torCompat' : Prop) (htorCompat' : torCompat')
    (orbCompat' : Prop) (horbCompat' : orbCompat')
    (secCompat' : Prop) (hsecCompat' : secCompat')
    (cusCompat' : Prop) (hcusCompat' : cusCompat') :
    (S1880PaperO l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume =
      (S1880PaperO l R' redCompat' hredCompat' torCompat' htorCompat'
        orbCompat' horbCompat' secCompat' hsecCompat' cusCompat'
        hcusCompat').qPilotLogVolume := by
  rw [s1880_paper_qPilotLogVolume_eq, s1880_paper_qPilotLogVolume_eq]

/-! ## 3. The paper-route original Theta-link and its xi-f ray membership -/

/-- **The paper-route O-layer Theta-link.**  For every supply R of the paper's
remaining Definition 3.1 clauses and every actual paper signed-hull datum D, the
actual paper-route object carries the original Theta-link structure at the
actual S1391 L-carrier C3. -/
theorem s1880_paper_thetaLink (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFThetaLinkActual
      (S1880PaperO l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat)
      D
      (S1880PaperC3 l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  s1684OrigXiFThetaLinkActual (l := l) R redCompat hredCompat torCompat
    htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D

/-- The concrete link_identification of the paper-route Theta-link: the object
scalar is the actual paper q-pilot scalar, and it is below the actual signed
theta hull log-volume.  Both conjuncts are proved, not assumed. -/
theorem s1880_paper_linkIdentification (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    (s1880_paper_thetaLink l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
      D).link_identification :=
  OrigXiFThetaLinkIdentification_of_fields
    (S1880PaperO l R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat)
    D
    (S1880PaperC3 l R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat)
    (S1527_origXiFScalarExactField l R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat (S1880PaperO l R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
    (S1554_signedHull_le l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)

/-- **The paper-route xi-f membership.**  The actual paper-route q-pilot scalar
lies in the ray R_{<= -|log Theta|} of the actual paper signed hull. -/
theorem s1880_paper_xiF_ray (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    (S1880PaperO l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume :=
  (s1880_paper_thetaLink l R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
    D).link_implies_inclusion
    (s1880_paper_linkIdentification l R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat D)

/-- **The paper-level original Theta-link xi-f, reduced to exactly one input.**
For every supply R of the paper's remaining Definition 3.1 clauses and every
actual paper signed-hull datum D, the paper-route object over the actual S1679
O(-D) carrier has the concrete link identification and the xi-f ray membership.
No other input is used. -/
theorem s1880_paper_xiF_core (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    (s1880_paper_thetaLink l R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
        D).link_identification ∧
      (S1880PaperO l R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume ∈
        hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume :=
  ⟨s1880_paper_linkIdentification l R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat D,
    s1880_paper_xiF_ray l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D⟩

/-! ## 4. The precise first missing object -/

/-- The paper's remaining Definition 3.1 clause supply over the actual S1280
Gaussian arithmetic: D5 torsion, D6 orbicurve, D7 sections, D8 cusp.  This is an
input type; no inhabitant exists in the tree. -/
abbrev S1880PaperClauseSupply (l : PrimeGeFive) :=
  S1280RemainingClauses l

/-- **The precise first missing field** of the paper-level original Theta-link
xi-f: the D5 torsion clause SourceTorsionClause.{0,0,0} l.  Its concrete content
is a rank-two l-torsion basis together with the SL_2 F_l large-image statement
for the actual curve, plus the residue-characteristic compatibility
l != residue characteristic of Definition 3.1(c). -/
abbrev S1880FirstMissing (l : PrimeGeFive) : Type 1 :=
  SourceTorsionClause.{0, 0, 0} l

/-- The first missing field is literally the torsion projection of the paper
clause supply: supplying the D5 clause is a necessary part of supplying the
paper input. -/
def s1880_firstMissing_of_supply (l : PrimeGeFive)
    (R : S1880PaperClauseSupply l) : S1880FirstMissing l :=
  R.torsion

/-- The D5 clause's own non-carrier field is a genuine proposition (the SL_2
large-image statement), not a True slot: every inhabitant of the clause supplies
a proof of it. -/
theorem s1880_firstMissing_imageContainsSL2 (l : PrimeGeFive)
    (T : S1880FirstMissing l) : T.imageContainsSL2 :=
  T.imageContainsSL2_proved

/-- The single non-actual field of the paper signed-hull datum: the paper
procession normalization (IUT III, Step (xi-d)/(xi-e)).  Both sides are
constructed actual quantities -- the normalized Haar log-volume of the actual
1,circ U theta hull and the actual determinant-procession average -- so this is a
proposition about actual objects, not a free real parameter. -/
theorem s1880_signedHullDatum_bridge {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    D.thetaHull.haar.logVolume D.thetaHull.compactHull.hull =
      ENNReal.ofReal D.determinant.procession.average :=
  D.hull_logVolume_eq_procession

/-- Given a paper signed-hull datum, the xi-f comparison is the comparison of two
actual quantities: the actual q-pilot scalar and minus the actual
determinant-procession average. -/
theorem s1880_signedHullDatum_comparison {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    -localLogMagnitude S1487Cand ≤ -D.determinant.procession.average := by
  rw [← OrigXiFSignedThetaHullLogVolume_eq_neg_average D]
  exact s1880_xiF_inequality D

/-! ## 5. Axiom probes -/

#print axioms s1880_xiF_inequality_abs
#print axioms s1880_xiF_inequality_strict
#print axioms s1880_xiF_ray
#print axioms s1880_xiF_paperSignedHullRay
#print axioms s1880_paper_qPilotLogVolume_eq
#print axioms s1880_paper_qPilotLogVolume_eq_neg_order_mul_log_five
#print axioms s1880_paper_qPilot_le_signedHull
#print axioms s1880_qPilotLogVolume_independent_of_supply
#print axioms s1880_paper_thetaLink
#print axioms s1880_paper_linkIdentification
#print axioms s1880_paper_xiF_ray
#print axioms s1880_paper_xiF_core
#print axioms s1880_firstMissing_of_supply
#print axioms s1880_signedHullDatum_bridge

end LeanFormal.IUT.XiFPaper.S1880OriginalXiFActual

end
