import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

/-!
# S1527: order equality for the actual S1280 Gaussian bad family

Layer: O (the original Theta-link / q-pilot scalar layer), on the actual
S1280 Gaussian source data.

## The target

S1487 reduced the S1463 scalar field

  scalar_eq : O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3

to the concrete equality

  sourceQPilotSignedLog I.initial = -localLogMagnitude S1487Cand

for a one-place bad family, and recorded that for the S1280 actual Gaussian
datum (singleton bad family at the place above 5, q-parameter
5 ^ (-order_bad)) the scalar equality reduces further to

  order_bad = order_C3,

where order_bad is the completed-DVR order of the S1280 bad-place
q-candidate and order_C3 is the order of the actual S1487/S1391 completion q
candidate at the same concrete Gaussian place.  The S1487 report left that
arithmetic equality open.

## What is proved here

1. The S1280 bad place is the singleton {concreteGaussianFivePlace}, and the
   section lift used by badPlaceQCandidate at that place is the place
   itself.  This is not an extra hypothesis: it follows from the proved
   restriction identity S1280_comap_eq_self and the proved section-lift
   compatibility sectionFiniteLift_comap.

2. Consequently the actual S1280 bad-place q-candidate is the same
   Classical.choice term as the S1487 completion q candidate:

     badPlaceQCandidate (S1280Selection l) b
       = S1487Cand   (after transporting along the proved place equality),

   hence

     order_bad = order_C3

   for every bad index b.  There is no remaining arithmetic equality at this
   point: the equality is definitional once the section lift is identified.

3. The actual q-parameter is computed:

     (S1280ReductionClause l).qParameter b = 5 ^ (-order_C3),

   and its absolute log is order_C3 * log 5.

4. For the S1280 assembled source data over ANY supply of the remaining
   Definition 3.1 clauses (D5 torsion, D6 orbicurve, D7 sections, D8 cusp) and
   the D9 compatibility pairs, the bad-family sum is

     sourceBadQAbsLog = order_C3 * log 5,

   while the actual S1391 L-carrier C3 at the same place has

     OrigXiFPaperQPilotLogVolume C3 = -(order_C3 * log 5).

   Therefore the S1463 scalar field holds:

     sourceQPilotSignedLog I.initial = OrigXiFPaperQPilotLogVolume C3,

   and for every paper q-pilot object O over that input,

     OrigXiFThetaLinkActualScalarExactField O C3.

5. The only remaining field of the full S1463 structure is the signed-hull
   comparison signedHull_le, which is a separate field; it is not assumed or
   proved here.  A constructor conditional on that field is recorded as
   S1527_origXiFThetaLinkActual.

## Boundary kept explicit

The D5-D9 source clauses are NOT constructed in the tree (S1280 records the
torsion clause as the first missing field).  The scalar theorems below are
therefore stated for an arbitrary supply R : S1280RemainingClauses l and
arbitrary D9 compatibility pairs; they do not fabricate that data and they do
not depend on its content.  The actual arithmetic, bad family, reduction
clause, completion q and C3 are all concrete and already present in the tree.

No unsound placeholder, no new logical assumption, no arbitrary inhabitant,
and no use of the scalar field as an input is present.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual

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

universe u uG uL uC uX

variable {l : PrimeGeFive}

local instance s1527GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1527FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The actual bad place and its section lift -/

/-- The canonical element of the S1280 bad-place singleton: the concrete
Gaussian place above 5. -/
noncomputable def S1527Bad0 (l : PrimeGeFive) : Bad (S1280Selection l) :=
  ⟨S1280Place l, by
    rw [S1280Selection_V_mod_bad]
    exact Set.mem_singleton _⟩

/-- The underlying place of any S1280 bad index is the concrete place above
5. -/
theorem S1527_bad_val_eq (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    b.1 = S1280Place l := by
  obtain ⟨p, hp⟩ := b
  have hp' : p = S1280Place l := by
    have h := hp
    rw [S1280Selection_V_mod_bad] at h
    exact Set.eq_of_mem_singleton h
  exact hp'

/-- The section lift used by the S1280 bad-place q-candidate is the concrete
place itself.  This uses only the proved restriction identity
S1280_comap_eq_self and the proved section-lift compatibility. -/
theorem S1527_sectionFiniteLift_eq (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    sectionFiniteLift (S1280Selection l) b.1 = S1280Place l := by
  have hb := S1527_bad_val_eq l b
  have hcomap := sectionFiniteLift_comap (S1280Selection l) b.1
  have hid := S1280_comap_eq_self l (sectionFiniteLift (S1280Selection l) b.1)
  exact (hid.symm.trans hcomap).trans hb

/-! ## 2. The order equality -/

/-- The completed-DVR order of the actual S1280 bad-place q-candidate. -/
noncomputable def S1527OrderBad (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : Nat :=
  (badPlaceQCandidate (S1280Selection l) b).order

/-- The completed-DVR order of the actual S1487/S1391 completion q candidate. -/
noncomputable def S1527OrderC3 : Nat :=
  S1487Cand.order

@[simp] theorem S1527OrderC3_eq : S1527OrderC3 = S1487Cand.order := rfl

/-- The S1280 bad-place candidate has exactly the S1487 completion candidate's
order.  The two Classical.choice terms are the same once the section lift is
identified with the concrete place. -/
theorem S1527_badPlaceQCandidate_order_eq (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (badPlaceQCandidate (S1280Selection l) b).order = S1487Cand.order := by
  have h := S1527_sectionFiniteLift_eq l b
  rw [show (badPlaceQCandidate (S1280Selection l) b).order =
      (Classical.choice (finitePlaceQCandidate_nonempty
        (sectionFiniteLift (S1280Selection l) b.1))).order from rfl]
  rw [h]
  rfl

/-- **The order equality order_bad = order_C3** for every S1280 bad index,
with no extra arithmetic hypothesis. -/
theorem S1527_order_bad_eq_order_C3 (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    S1527OrderBad l b = S1527OrderC3 := by
  unfold S1527OrderBad S1527OrderC3
  exact S1527_badPlaceQCandidate_order_eq l b

/-- The actual S1280 q-parameter computed through order_C3:
qParameter b = (1/5) ^ order_C3. -/
theorem S1527_qParameter_eq (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280ReductionClause l).qParameter b =
      ((5 : ℝ)⁻¹) ^ S1527OrderC3 := by
  rw [S1280ReductionClause_qParameter_eq l b, S1527_badPlaceQCandidate_order_eq l b,
    S1527OrderC3_eq]

/-! ## 3. The bad-family absolute log -/

/-- Numerical lemma: for positive n, |log ((1/5)^n)| = n * log 5. -/
theorem S1527_abs_log_inv_five_pow (n : Nat) (hn : 0 < n) :
    |Real.log (((5 : ℝ)⁻¹) ^ n)| = (n : ℝ) * Real.log 5 := by
  rw [Real.log_pow, Real.log_inv]
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hneg : (n : ℝ) * -Real.log 5 < 0 := by nlinarith
  rw [abs_of_neg hneg]
  ring

/-- The absolute log of the actual S1280 bad q-parameter is
order_C3 * log 5. -/
theorem S1527_abs_log_qParameter (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    |Real.log ((S1280ReductionClause l).qParameter b)| =
      (S1527OrderC3 : ℝ) * Real.log 5 := by
  rw [S1527_qParameter_eq]
  exact S1527_abs_log_inv_five_pow S1527OrderC3 S1487Cand.order_pos

/-- Each actual S1280 bad-family summand is exactly the actual C3 local log
magnitude. -/
theorem S1527_abs_log_qParameter_eq_localLogMagnitude (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    |Real.log ((S1280ReductionClause l).qParameter b)| =
      localLogMagnitude S1487Cand := by
  rw [S1527_abs_log_qParameter, S1527OrderC3_eq, ← S1487Cand_magnitude]

/-! ## 4. The S1280 assembled source data and the O-layer scalar -/

/-- The S1280 assembled Definition 3.1 source data over an arbitrary supply of
the remaining clauses. -/
noncomputable def S1527SourceData (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    SourceDefinition31Data l :=
  S1280SourceData_of_remaining l R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

/-- The concrete shear OriginalInput over the S1280 assembled source data. -/
noncomputable def S1527Input (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OriginalInput.{0, 0, 0, 0, 0} l S1487W :=
  S1487OriginalInput (l := l)
    (S1527SourceData l R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat)

@[simp] theorem S1527Input_initial (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1527Input l R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat).initial =
      S1527SourceData l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat := rfl

/-- The actual S1391 L-carrier C3 at the S1280 Gaussian place, over the S1280
assembled input. -/
noncomputable def S1527C3 (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    SourcePilotRegionDataL (I := S1527Input l R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  actualSourcePilotRegionDataL (I := S1527Input l R redCompat hredCompat torCompat
    htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
    S1487FivePlace

/-- The actual C3 carries the S1487 completion q candidate. -/
theorem S1527C3_q (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat).q = S1487Cand := rfl

/-- The paper q-pilot log-volume of the actual C3 is
-localLogMagnitude S1487Cand = -(order_C3 * log 5). -/
theorem S1527C3_logVolume (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OrigXiFPaperQPilotLogVolume
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat) =
      -localLogMagnitude S1487Cand := by
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm, S1527C3_q, localLogMagnitude,
    localSignedLog, neg_neg]
  rfl

/-- The bad-family absolute-log sum of the S1280 source data is
order_C3 * log 5. -/
theorem S1527_sourceBadQAbsLog (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    sourceBadQAbsLog
      (S1527SourceData l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      (S1527OrderC3 : ℝ) * Real.log 5 := by
  haveI : Subsingleton (Bad (S1280Selection l)) := S1280Bad_subsingleton l
  unfold sourceBadQAbsLog
  change (∑ b : Bad (S1280Selection l),
      |Real.log ((S1280ReductionClause l).qParameter b)|) =
    (S1527OrderC3 : ℝ) * Real.log 5
  rw [Fintype.sum_eq_single (S1527Bad0 l)]
  · exact S1527_abs_log_qParameter l (S1527Bad0 l)
  · intro x hx
    exact absurd (Subsingleton.elim x (S1527Bad0 l)) hx

/-- The S1280 bad-family sum is exactly the S1487/S1391 local magnitude. -/
theorem S1527_sourceBadQAbsLog_eq_localLogMagnitude (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    sourceBadQAbsLog
      (S1527SourceData l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      localLogMagnitude S1487Cand := by
  rw [S1527_sourceBadQAbsLog, S1527OrderC3_eq, ← S1487Cand_magnitude]

/-- **S1463 scalar field for the actual S1280 Gaussian bad family.**  The
bad-family q-log sum equals the actual C3 q-pilot scalar. -/
theorem S1527_scalar_eq (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OrigXiFPaperQPilotScalarExactFirstField
      (I := S1527Input l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat) := by
  unfold OrigXiFPaperQPilotScalarExactFirstField sourceQPilotSignedLog
  rw [S1527Input_initial, S1527_sourceBadQAbsLog, S1527C3_logVolume,
    S1487Cand_magnitude, S1527OrderC3_eq]

/-- The S1463 scalar field, in the O.qPilotLogVolume form, for every paper
q-pilot object over the S1280 assembled input. -/
theorem S1527_origXiFScalarExactField (l : PrimeGeFive)
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
        horbCompat secCompat hsecCompat cusCompat hcusCompat) G envStrip) :
    OrigXiFThetaLinkActualScalarExactField O
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat) := by
  unfold OrigXiFThetaLinkActualScalarExactField
  rw [O.qPilotLogVolume_eq]
  exact S1527_scalar_eq l R redCompat hredCompat torCompat htorCompat orbCompat
    horbCompat secCompat hsecCompat cusCompat hcusCompat

/-- The full S1463 structure, conditional only on the separate signed-hull
comparison field. -/
theorem S1527_origXiFThetaLinkActual (l : PrimeGeFive)
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
    (D : OrigXiFPaperSignedHullData X l)
    (hcomparison : OrigXiFPaperQPilotLogVolume
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat) ≤
      OrigXiFSignedThetaHullLogVolume D) :
    OrigXiFThetaLinkActual O D
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat) :=
  origXiFThetaLinkActualOf O D _
    (S1527_origXiFScalarExactField l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat O)
    hcomparison

/-! ## 5. Axiom probes -/

#print axioms S1527_order_bad_eq_order_C3
#print axioms S1527_qParameter_eq
#print axioms S1527_abs_log_qParameter
#print axioms S1527_sourceBadQAbsLog
#print axioms S1527_scalar_eq
#print axioms S1527_origXiFScalarExactField
#print axioms S1527_origXiFThetaLinkActual

end LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual

end
