import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import tmp.sheaf.xif.paper.OrigXiFThetaLinkActual
import tmp.sheaf.xif.paper.OrigXiFPaperSignedHullActual
import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# S1921: the q-pilot scalar bridge from S1895PaperO to S1880PaperO

Layer: **O** (original Theta-link / q-pilot scalar), on the actual S1280
Gaussian source data and the actual S1391 L-carrier C3.

## Target and result

S1895PaperO D is the paper-faithful rebased object of S1895: its
qPilotLogVolume is definitionally sourceQPilotSignedLog (I D).initial.
S1880PaperO is the S1684 paper-route object over the same S1527 input: S1880
proved its qPilotLogVolume is the actual completion scalar
-localLogMagnitude S1487Cand = -abs(log(norm q)) = -(order_C3 * log 5).

The two objects have different strips (S1895 proved no FPrimeStripEquiv
exists between the concrete finite-local strip of S1880PaperO and the paper
(1,0) core, s1895FirstMissing_impossible).  The q-pilot scalar, however,
is a Real field and both sides reduce to the same actual completion scalar.
This file proves that scalar equality (and both evaluations) with no new
hypothesis, no sorry, no axiom and no True/PUnit placeholder:

* s1921_qPilotLogVolume_eq_s1880:
  (S1895PaperO D).qPilotLogVolume = (S1895S1880O D).qPilotLogVolume;
* the common value is -localLogMagnitude S1487Cand, -abs(log(norm q)), and
  -(order_C3 * log 5);
* it is also the actual C3 paper scalar OrigXiFPaperQPilotLogVolume (C3 D)
  (s1921_qPilotLogVolume_eq_C3), which is the S1527/S1487 scalar alignment.

## The bridge for S1920

The two exact scalar fields of the S1463 O-layer Theta-link are provided for
S1895PaperO and the actual C3:

* s1921_scalarExactField (the scalar_eq field, from S1527);
* s1921_comparisonExactField (the signedHull_le field: the S1527 C3 scalar
evaluation plus the S1880 xi-f inequality).

Their consequences s1921_qPilotLogVolume_le_signedHull,
s1921_qPilotLogVolume_lt_signedHull and s1921_qPilotLogVolume_mem_ray are
the xi-f scalar comparison on S1895PaperO itself.  These are exactly the two
exact scalar fields that assemble into OrigXiFThetaLinkActual
(S1895PaperO D) D' (C3 D); this file records and checks the scalar half,
without claiming object or strip identification.

## Boundary kept explicit

This is a scalar bridge only.  It does not assert an FPrimeStripEquiv, a
log-Kummer identification, or an identification of S1880PaperO with
S1895PaperO.  By S1895 the strip identification is impossible; only the
q-pilot log-volume is compared, because that is the quantity S1920's xi-f
comparison consumes.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1921S1895ScalarActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1880OriginalXiFActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual

universe uX

local instance s1921GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1921FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The actual C3 of the S1895 input -/

/-- The actual S1391 L-carrier C3 of the S1895 paper input: S1527C3 at the
same remaining-clause supply and D9 compatibility pairs. -/
noncomputable abbrev s1921C3 (D : S1895PaperInput) :
    SourcePilotRegionDataL (I := S1895PaperInput.I D) :=
  S1527C3 D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
    D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat D.hcusCompat

/-! ## 2. The scalar equality between the two paper O objects -/

/-- **The S1895PaperO and S1880PaperO q-pilot log-volumes are equal.**  Both
are the actual completion scalar -localLogMagnitude S1487Cand; the proof only
uses the two objects' proved scalar evaluations, not their differing strips. -/
theorem s1921_qPilotLogVolume_eq_s1880 (D : S1895PaperInput) :
    (S1895PaperO D).qPilotLogVolume = (S1895S1880O D).qPilotLogVolume := by
  rw [s1895PaperO_qPilot_eq]
  exact (s1880_paper_qPilotLogVolume_eq D.l D.R D.redCompat D.hredCompat
    D.torCompat D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat
    D.cusCompat D.hcusCompat).symm

/-- The same equality with S1880PaperO written in its explicit-argument form. -/
theorem s1921_qPilotLogVolume_eq_s1880_explicit (D : S1895PaperInput) :
    (S1895PaperO D).qPilotLogVolume =
      (S1880PaperO D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
        D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat
        D.hcusCompat).qPilotLogVolume :=
  s1921_qPilotLogVolume_eq_s1880 D

/-! ## 3. The common scalar: S1487 completion magnitude and arithmetic value -/

/-- The S1895 object's scalar is the actual S1487 completion magnitude. -/
theorem s1921_qPilotLogVolume_eq_neg_localLogMagnitude (D : S1895PaperInput) :
    (S1895PaperO D).qPilotLogVolume = -localLogMagnitude S1487Cand :=
  s1895PaperO_qPilot_eq D

/-- The S1880 object's scalar is the same actual S1487 completion magnitude. -/
theorem s1921_s1880_qPilotLogVolume_eq_neg_localLogMagnitude
    (D : S1895PaperInput) :
    (S1895S1880O D).qPilotLogVolume = -localLogMagnitude S1487Cand :=
  s1880_paper_qPilotLogVolume_eq D.l D.R D.redCompat D.hredCompat D.torCompat
    D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat
    D.hcusCompat

/-- The S1895PaperO scalar is the paper -abs(log(norm q)) of the actual
completion q. -/
theorem s1921_qPilotLogVolume_eq_neg_abs_log_q (D : S1895PaperInput) :
    (S1895PaperO D).qPilotLogVolume = -|Real.log ‖S1487Cand.q‖| := by
  rw [s1921_qPilotLogVolume_eq_neg_localLogMagnitude,
    s1880_abs_log_q_eq_magnitude]

/-- The S1880PaperO scalar is the same paper -abs(log(norm q)). -/
theorem s1921_s1880_qPilotLogVolume_eq_neg_abs_log_q (D : S1895PaperInput) :
    (S1895S1880O D).qPilotLogVolume = -|Real.log ‖S1487Cand.q‖| := by
  rw [s1921_s1880_qPilotLogVolume_eq_neg_localLogMagnitude,
    s1880_abs_log_q_eq_magnitude]

/-- The S1895PaperO scalar is the arithmetic value -(order_C3 * log 5). -/
theorem s1921_qPilotLogVolume_eq_neg_order_mul_log_five
    (D : S1895PaperInput) :
    (S1895PaperO D).qPilotLogVolume = -((S1487Cand.order : ℝ) * Real.log 5) := by
  rw [s1921_qPilotLogVolume_eq_neg_localLogMagnitude, S1487Cand_magnitude]

/-- The S1880PaperO scalar is the same arithmetic value -(order_C3 * log 5). -/
theorem s1921_s1880_qPilotLogVolume_eq_neg_order_mul_log_five
    (D : S1895PaperInput) :
    (S1895S1880O D).qPilotLogVolume = -((S1487Cand.order : ℝ) * Real.log 5) :=
  s1880_paper_qPilotLogVolume_eq_neg_order_mul_log_five D.l D.R D.redCompat
    D.hredCompat D.torCompat D.htorCompat D.orbCompat D.horbCompat D.secCompat
    D.hsecCompat D.cusCompat D.hcusCompat

/-! ## 4. Alignment with the S1527/S1487 C3 scalar -/

/-- The S1895PaperO scalar is the actual C3 paper q-pilot scalar
OrigXiFPaperQPilotLogVolume (s1921C3 D). -/
theorem s1921_qPilotLogVolume_eq_C3 (D : S1895PaperInput) :
    (S1895PaperO D).qPilotLogVolume = OrigXiFPaperQPilotLogVolume (s1921C3 D) := by
  rw [s1921_qPilotLogVolume_eq_neg_localLogMagnitude]
  exact (S1527C3_logVolume D.l D.R D.redCompat D.hredCompat D.torCompat
    D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat
    D.hcusCompat).symm

/-- The S1880PaperO scalar is the same actual C3 paper q-pilot scalar. -/
theorem s1921_s1880_qPilotLogVolume_eq_C3 (D : S1895PaperInput) :
    (S1895S1880O D).qPilotLogVolume = OrigXiFPaperQPilotLogVolume (s1921C3 D) := by
  rw [s1921_s1880_qPilotLogVolume_eq_neg_localLogMagnitude]
  exact (S1527C3_logVolume D.l D.R D.redCompat D.hredCompat D.torCompat
    D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat
    D.hcusCompat).symm

/-! ## 5. The two exact scalar fields of the S1463 Theta-link -/

/-- **The S1463 scalar_eq field for S1895PaperO**: the object scalar is the
actual C3 paper q-pilot scalar (S1527 arithmetic). -/
theorem s1921_scalarExactField (D : S1895PaperInput) :
    OrigXiFThetaLinkActualScalarExactField (S1895PaperO D) (s1921C3 D) :=
  S1527_origXiFScalarExactField D.l D.R D.redCompat D.hredCompat D.torCompat
    D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat
    D.hcusCompat (S1895PaperO D)

/-- **The S1463 signedHull_le field for S1895PaperO's C3**: the actual C3
scalar is at most the actual signed theta hull log-volume, for every actual
paper signed-hull datum.  The C3 scalar is evaluated by the S1527 arithmetic
and the comparison is the S1880 xi-f inequality. -/
theorem s1921_comparisonExactField (D : S1895PaperInput)
    {X : Type uX} [TopologicalSpace X]
    (Dh : OrigXiFPaperSignedHullData X D.l) :
    OrigXiFThetaLinkActualComparisonExactField Dh (s1921C3 D) := by
  change OrigXiFPaperQPilotLogVolume
      (S1527C3 D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
        D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat
        D.hcusCompat) ≤ OrigXiFSignedThetaHullLogVolume Dh
  rw [S1527C3_logVolume D.l D.R D.redCompat D.hredCompat D.torCompat
    D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat
    D.hcusCompat]
  exact s1880_xiF_inequality Dh

/-- The two exact scalar fields hold simultaneously for S1895PaperO and its
actual C3; this conjunction is the scalar bridge S1920 consumes. -/
theorem s1921_thetaLinkScalarFields (D : S1895PaperInput)
    {X : Type uX} [TopologicalSpace X]
    (Dh : OrigXiFPaperSignedHullData X D.l) :
    OrigXiFThetaLinkActualScalarExactField (S1895PaperO D) (s1921C3 D) ∧
      OrigXiFThetaLinkActualComparisonExactField Dh (s1921C3 D) :=
  ⟨s1921_scalarExactField D, s1921_comparisonExactField D Dh⟩

/-! ## 6. The xi-f scalar comparison on S1895PaperO -/

/-- **The xi-f scalar comparison for S1895PaperO**: its q-pilot log-volume is
at most the actual signed theta-hull log-volume.  This is the S1880 xi-f
inequality transported along the scalar equality of section 2. -/
theorem s1921_qPilotLogVolume_le_signedHull (D : S1895PaperInput)
    {X : Type uX} [TopologicalSpace X]
    (Dh : OrigXiFPaperSignedHullData X D.l) :
    (S1895PaperO D).qPilotLogVolume ≤ OrigXiFSignedThetaHullLogVolume Dh := by
  rw [s1921_qPilotLogVolume_eq_neg_localLogMagnitude]
  exact s1880_xiF_inequality Dh

/-- The same comparison through the C3 scalar field, showing the exact field
used by the Theta-link consumer. -/
theorem s1921_qPilotLogVolume_le_signedHull_via_C3 (D : S1895PaperInput)
    {X : Type uX} [TopologicalSpace X]
    (Dh : OrigXiFPaperSignedHullData X D.l) :
    (S1895PaperO D).qPilotLogVolume ≤ OrigXiFSignedThetaHullLogVolume Dh := by
  rw [s1921_qPilotLogVolume_eq_C3]
  exact s1921_comparisonExactField D Dh

/-- The xi-f comparison is strict: the actual completion scalar is below -1
while the actual signed theta hull log-volume is at least -1. -/
theorem s1921_qPilotLogVolume_lt_signedHull (D : S1895PaperInput)
    {X : Type uX} [TopologicalSpace X]
    (Dh : OrigXiFPaperSignedHullData X D.l) :
    (S1895PaperO D).qPilotLogVolume < OrigXiFSignedThetaHullLogVolume Dh := by
  rw [s1921_qPilotLogVolume_eq_neg_localLogMagnitude,
    ← s1880_abs_log_q_eq_magnitude]
  exact s1880_xiF_inequality_strict Dh

/-- **The xi-f ray membership**: the S1895PaperO q-pilot scalar lies in the
paper ray R_{<= -abs(log Theta)} of the actual signed theta hull. -/
theorem s1921_qPilotLogVolume_mem_ray (D : S1895PaperInput)
    {X : Type uX} [TopologicalSpace X]
    (Dh : OrigXiFPaperSignedHullData X D.l) :
    (S1895PaperO D).qPilotLogVolume ∈ OrigXiFThetaHullLogVolumeRay Dh :=
  (OrigXiFmem_thetaHullLogVolumeRay_iff Dh).mpr
    (s1921_qPilotLogVolume_le_signedHull D Dh)

/-! ## 7. Axiom probes -/

#print axioms s1921_qPilotLogVolume_eq_s1880
#print axioms s1921_qPilotLogVolume_eq_neg_localLogMagnitude
#print axioms s1921_s1880_qPilotLogVolume_eq_neg_localLogMagnitude
#print axioms s1921_qPilotLogVolume_eq_neg_abs_log_q
#print axioms s1921_qPilotLogVolume_eq_neg_order_mul_log_five
#print axioms s1921_qPilotLogVolume_eq_C3
#print axioms s1921_scalarExactField
#print axioms s1921_comparisonExactField
#print axioms s1921_qPilotLogVolume_le_signedHull
#print axioms s1921_qPilotLogVolume_lt_signedHull
#print axioms s1921_qPilotLogVolume_mem_ray

end LeanFormal.IUT.XiFPaper.S1921S1895ScalarActual

end
