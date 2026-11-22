import tmp.sheaf.xif.paper.S1527OOrderEqualityActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.xif.paper.S1477OScalarBridgeActual

/-!
# S1554: the signed-hull comparison from the actual S1280 q-parameter

Layer: O (original-text Theta-link / q-pilot scalar layer), on the actual
S1280 Gaussian source data and the actual S1391 L-carrier C3.

## Target

S1463 (OrigXiFThetaLinkActual) carries two exact scalar fields

  scalar_eq     : O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3
  signedHull_le : OrigXiFPaperQPilotLogVolume C3 <= OrigXiFSignedThetaHullLogVolume D

S1527 already proved scalar_eq for the actual S1280 assembled data and the
actual C3 at the concrete Gaussian place above 5, and computed the actual
bad-place q-parameter

  (S1280ReductionClause l).qParameter b = 5 ^ (-order_C3),   order_C3 >= 1.

S1477 proved the abstract conditional step

  OrigXiFPaperQPilotLogVolume C3 <= -1  ->  signedHull_le for every actual D,

using the actual theta-hull compactness/normalization bound
OrigXiFSignedThetaHullLogVolume_ge_neg_one; S1477 left the numeric input
<= -1 open.  This file discharges it from the S1527 arithmetic, so that no
signedHull_le hypothesis remains.

## What is proved here

1. log 5 > 1 (S1554_one_lt_log_five), from Mathlib's Real.exp_one_lt_three.
2. The S1527 q-parameter computation gives, for every bad index b,

     |log ((S1280ReductionClause l).qParameter b)| = order_C3 * log 5,

   which is exactly the actual S1487/S1391 completion log magnitude
   localLogMagnitude S1487Cand (S1554_qParameter_abs_log_eq_qPilotLogVolume).
3. Consequently, for the actual C3,

     OrigXiFPaperQPilotLogVolume C3 = -(order_C3 * log 5) <= -log 5 < -1

   (S1554_qPilotLogVolume_eq_neg_order_mul_log_five,
   S1554_qPilotLogVolume_le_neg_log_five,
   S1554_qPilotLogVolume_lt_neg_one).
4. The numeric hypothesis of the S1477 bridge is therefore satisfied, and
   signedHull_le holds for EVERY actual signed hull datum D
   (S1554_signedHull_le), with no signedHull_le or <= -1 hypothesis.
5. Combining this comparison with the S1527 scalar field constructs the full
   S1463 structure

     OrigXiFThetaLinkActual O D C3

   for every paper q-pilot object O over the S1527 assembled input and every
   actual D (S1554_origXiFThetaLinkActual).

## Boundary kept explicit

The D5-D9 source clauses remain the S1280RemainingClauses supply of S1527 and
D9 compatibility pairs are arbitrary; no new theorem uses their content.  The
arithmetic positivity 0 < order_C3, the residue norm 5 and the theta-hull
normalization -|log Theta| >= -1 are actual tree theorems, not assumptions.
No sorry, axiom, added hypothesis, or arbitrary inhabitant is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1554SignedHullFromQActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual

universe u uG uL uC uX

variable {l : PrimeGeFive}

local instance s1554GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1554FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. Numerics: log 5 > 1 -/

/-- log 5 > 1: Mathlib's exp 1 < 3 < 5. -/
theorem S1554_one_lt_log_five : (1 : ℝ) < Real.log 5 := by
  have h5 : Real.exp 1 < 5 := lt_trans Real.exp_one_lt_three (by norm_num)
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) h5

/-- Hence -log 5 < -1. -/
theorem S1554_neg_log_five_lt_neg_one : -Real.log 5 < -1 := by
  have h := S1554_one_lt_log_five
  linarith

/-- The actual S1487/S1391 completion log magnitude is order_C3 * log 5,
so in particular -localLogMagnitude S1487Cand <= -log 5. -/
theorem S1554_neg_localLogMagnitude_le_neg_log_five :
    -localLogMagnitude S1487Cand ≤ -Real.log 5 := by
  have horder : (1 : ℝ) ≤ (S1487Cand.order : ℝ) := by
    exact_mod_cast S1487Cand.order_pos
  have hlogpos : (0 : ℝ) < Real.log 5 := Real.log_pos (by norm_num)
  have hmul : Real.log 5 ≤ (S1487Cand.order : ℝ) * Real.log 5 := by
    have h := mul_le_mul_of_nonneg_right horder hlogpos.le
    simpa using h
  rw [S1487Cand_magnitude]
  linarith

/-- The actual completion scalar is strictly below -1. -/
theorem S1554_neg_localLogMagnitude_lt_neg_one :
    -localLogMagnitude S1487Cand < -1 := by
  have h1 := S1554_neg_localLogMagnitude_le_neg_log_five
  have h2 := S1554_neg_log_five_lt_neg_one
  linarith

/-- The actual completion scalar is at most -1. -/
theorem S1554_neg_localLogMagnitude_le_neg_one :
    -localLogMagnitude S1487Cand ≤ -1 :=
  S1554_neg_localLogMagnitude_lt_neg_one.le

/-! ## 2. The actual bad-place q-parameter against the actual C3 scalar -/

/-- The absolute log of the actual S1280 bad-place q-parameter is
order_C3 * log 5; this is S1527_abs_log_qParameter with order_bad and
order_C3 identified definitionally. -/
theorem S1554_qParameter_abs_log (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    |Real.log ((S1280ReductionClause l).qParameter b)| =
      (S1487Cand.order : ℝ) * Real.log 5 := by
  rw [S1527_abs_log_qParameter]
  rfl

/-- The bad-place q-parameter is exactly the actual S1391 C3 q-pilot scalar:
-|log qParameter b| = OrigXiFPaperQPilotLogVolume C3. -/
theorem S1554_qParameter_abs_log_eq_qPilotLogVolume (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (b : Bad (S1280Selection l)) :
    -|Real.log ((S1280ReductionClause l).qParameter b)| =
      OrigXiFPaperQPilotLogVolume
        (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat) := by
  rw [S1554_qParameter_abs_log, S1527C3_logVolume, S1487Cand_magnitude]

/-! ## 3. The C3 q-pilot scalar is at most -log 5 < -1 -/

/-- **Arithmetic evaluation of the actual C3 scalar**:
OrigXiFPaperQPilotLogVolume C3 = -(order_C3 * log 5), the S1527
qParameter = 5^(-order_C3) computation. -/
theorem S1554_qPilotLogVolume_eq_neg_order_mul_log_five (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OrigXiFPaperQPilotLogVolume
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      -((S1487Cand.order : ℝ) * Real.log 5) := by
  rw [S1527C3_logVolume, S1487Cand_magnitude]

/-- The actual C3 q-pilot scalar is at most -log 5. -/
theorem S1554_qPilotLogVolume_le_neg_log_five (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OrigXiFPaperQPilotLogVolume
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) ≤
      -Real.log 5 := by
  rw [S1527C3_logVolume]
  exact S1554_neg_localLogMagnitude_le_neg_log_five

/-- The actual C3 q-pilot scalar is strictly below -1. -/
theorem S1554_qPilotLogVolume_lt_neg_one (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OrigXiFPaperQPilotLogVolume
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) < -1 := by
  rw [S1527C3_logVolume]
  exact S1554_neg_localLogMagnitude_lt_neg_one

/-- **The numeric hypothesis of the S1477 bridge is discharged for the actual
S1280 data**: the actual C3 q-pilot scalar is at most -1. -/
theorem S1554_qPilotLogVolume_le_neg_one (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OrigXiFPaperQPilotLogVolume
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) ≤ -1 :=
  (S1554_qPilotLogVolume_lt_neg_one l R redCompat hredCompat torCompat
    htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
    hcusCompat).le

/-! ## 4. signedHull_le for every actual D -/

/-- **The signed-hull comparison of S1463 holds for every actual signed hull
datum D**, with no signedHull_le assumption: the actual q-pilot scalar is
<= -1 by the S1527/S1487 arithmetic, while the actual signed theta hull
log-volume is -|log Theta| >= -1 by the actual theta-hull compactness
normalization (OrigXiFSignedThetaHullLogVolume_ge_neg_one). -/
theorem S1554_signedHull_le (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFPaperQPilotLogVolume
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) ≤
      OrigXiFSignedThetaHullLogVolume D :=
  LeanFormal.IUT.XiFPaper.S1477OScalarBridgeActual.origXiFOSignedHullExactField_of_qPilotLogVolume_le_neg_one
    (S1527Input l R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat)
    D
    (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat)
    (S1554_qPilotLogVolume_le_neg_one l R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)

/-- The same comparison in the direct two-ingredient form, recorded for
auditability: qPilotLogVolume C3 <= -1 <= signedThetaHullLogVolume D. -/
theorem S1554_signedHull_le_via_bound (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFPaperQPilotLogVolume
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) ≤
      OrigXiFSignedThetaHullLogVolume D :=
  le_trans
    (S1554_qPilotLogVolume_le_neg_one l R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
    (OrigXiFSignedThetaHullLogVolume_ge_neg_one D)

/-! ## 5. The full S1463 structure, with no signed-hull hypothesis -/

/-- **The full OrigXiFThetaLinkActual for the actual S1280 Gaussian data.**
For every paper q-pilot object O over the S1527 assembled input and every
actual signed hull datum D, the two exact scalar fields hold: scalar_eq
from S1527_origXiFScalarExactField and signedHull_le from
S1554_signedHull_le.  No field is assumed. -/
theorem S1554_origXiFThetaLinkActual (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {G : Type uG} [Group G] [TopologicalSpace G]
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {envStrip : FPrimeStrip S1487W}
    (O : PaperQPilotObject (Label := Label) (Choice := Choice)
      (S1527Input l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) G envStrip)
    {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFThetaLinkActual O D
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  origXiFThetaLinkActualOf O D
    (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat)
    (S1527_origXiFScalarExactField l R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat O)
    (S1554_signedHull_le l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)

/-! ## 6. Axiom probes -/

#print axioms S1554_one_lt_log_five
#print axioms S1554_qParameter_abs_log
#print axioms S1554_qParameter_abs_log_eq_qPilotLogVolume
#print axioms S1554_qPilotLogVolume_eq_neg_order_mul_log_five
#print axioms S1554_qPilotLogVolume_le_neg_log_five
#print axioms S1554_qPilotLogVolume_lt_neg_one
#print axioms S1554_qPilotLogVolume_le_neg_one
#print axioms S1554_signedHull_le
#print axioms S1554_signedHull_le_via_bound
#print axioms S1554_origXiFThetaLinkActual

end LeanFormal.IUT.XiFPaper.S1554SignedHullFromQActual

end
