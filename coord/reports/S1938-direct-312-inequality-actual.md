# S1938: Corollary 3.12 target inequality proved directly (no S1904 bridge)

Date: 2026-11-01.  Task: prove the Corollary 3.12 target inequality

    -|log q| <= -average,   equivalently   average <= |log q|,

at the actual q (qPilot = -|log q|, |log q| = localLogMagnitude S1487Cand) and
the actual S1903 determinant average, directly from the S1928 closed form,
without passing through the S1904 procession bridge; or give the exact first
missing.  No fake, no new hypothesis, no change of objects.

## Result (short)

**The target inequality is a theorem; there is no missing inequality.**
EXIT=0, zero errors, zero warnings, axioms [propext, Classical.choice,
Quot.sound] on every probed declaration.  The proof is finite arithmetic on the
S1928 average formula plus the S1487 evaluation of the actual q; it never uses
the S1904 bridge, the S1902 hull, or the S1880 >= -1 comparison.

Sharpened numerical chain (all kernel-checked, all unconditional in l):

    average = log 5 * (sum_j j^2) / l^4          (S1928, s1928_average_eq)
            <= log 5 * l^3 / l^4 = log 5 / l     (sum_j j^2 <= l^3)
            <= log 5 / 5                         (l >= 5)
            <  1                                 (log 5 <= 4)
            <  log 5 <= |log q|                  (S1487: localLogMagnitude >= log 5)

so the target inequality is strict, with a large margin (average < 1 while
|log q| >= log 5 > 1).

Why sum_j j^2 <= l^3: the signed labels are { j : Int // |j| <= lStar l } with
lStar l = (l-1)/2, and there are exactly l of them (SignedLabel.card_signedLabel).
Hence every square is <= lStar^2 <= l^2 and the sum of l terms is <= l * l^2.
(Exact value: sum_j j^2 = l(l^2-1)/12, not needed here.)

## What is proved (Lean, kernel-closed)

Target and its forms:

* S1938Target : PrimeGeFive -> Prop      (the named target)
* s1938_target : S1938Target l           (the named target is a theorem)
* s1938_average_le_abs_log_q :
      average <= |Real.log ||S1487Cand.q||
* s1938_neg_abs_log_q_le_neg_average :
      -|Real.log ||S1487Cand.q||| <= -average        (paper form)
* s1938_neg_magnitude_le_neg_average :
      -localLogMagnitude S1487Cand <= -average
* s1938_average_lt_abs_log_q : average < |log q|    (strictness)
* s1938_target_not_missing : not (|log q| < average)
* s1938_direct312 : conjunction of the two forms with average < 1

Sharp quantitative bounds on the actual S1903 average:

* s1938_sum_sq_le : sum_j (j.1)^2 <= l^3
* s1938_average_le_log_five_div : average <= log 5 / l
* s1938_average_le_log_five_div_five : average <= log 5 / 5
* s1938_log_five_div_five_lt_one : log 5 / 5 < 1
* s1938_average_lt_one : average < 1
  (S1904 gets average <= 1 only *under* the bridge; here it is unconditional
  at the actual S1903 determinant)

General interface for the paper-faithful determinant (S1939):

* s1938_neg_abs_log_q_le_neg_average_of_le :
      average P <= log 5  ->  -|log q| <= -average P
* s1938_neg_abs_log_q_le_neg_average_of_average_le_one :
      average P <= 1      ->  -|log q| <= -average P

Independence from the bridge, and the S1905 datum:

* s1938_inequality_without_bridge :
      s1915ClosedForm T <= 0  ->
        (average <= |log q|)  AND  not (S1904ProcessionBridge (S1902 hull) (S1903 det))
  i.e. on the S1928 clipped region (when nonempty) the bridge is false while the
  inequality holds: the inequality is strictly weaker than the bridge and cannot
  recover it there.
* s1938_S1905D_signed : OrigXiFSignedThetaHullLogVolume (S1905D T h) = -average
* s1938_S1905D_inequality :
      -|log q| <= OrigXiFSignedThetaHullLogVolume (S1905D T h)
* s1938_S1905D_inequality_magnitude : same in localLogMagnitude form
  The witness h is used only to *form* the datum; the proof does not use the
  bridge equation, it evaluates the signed scalar to -average and applies the
  numerical bound.

## Reading of the result (for the coordinator)

* The inequality content of 3.12 at the S1903 determinant is *trivial*
  numerically (average <= log 5/5 < 1 < log 5 <= |log q|).  S1905's
  equivalence (unconditional form <-> bridge) is a property of the assembled
  three-field datum, not of the inequality: a datum cannot exist without the
  bridge, but the inequality itself does not need it.
* Therefore S1939 (the paper-faithful determinant built from the actual root
  packet) does not need to prove the S1904 bridge to obtain 3.12's inequality:
  it only has to establish the determinant-side normalization
  average <= 1 (equivalently <= log 5).  That is the interface proved in
  section 4 of the Lean file.
* This file does NOT claim that s1903ActualDeterminant l is the paper's
  actual root-packet determinant.  S1928 computes its average as a rational
  multiple of log 5 with zero rational part and reduces the bridge at the
  actual fields to a genuine arithmetic identity, so S1939's determinant is
  still the paper-faithful one.  The S1904 bridge itself also remains open.

## Lean artifacts

Target file (UTF-8, no sorry/admit/axiom/True/PUnit):

  tmp/sheaf/xif/paper/S1938Direct312InequalityActual.lean
  bytes 20231, lines 431
  SHA256 B5DC84B87BA4BEFF91CB55CFF4F19CA24D044A97BCEFEA88008C675108095460

Compile (from D:/lean), final run:

  lake env lean -R D:/lean -s 65536 -M 8192 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1938Direct312InequalityActual.olean tmp/sheaf/xif/paper/S1938Direct312InequalityActual.lean

  EXIT=0, zero errors, zero warnings.
  Compile log: tmp/sheaf/xif/paper/_S1938compile.log (3265 bytes).
  Axiom probes (22 declarations, printed in the log): all
  [propext, Classical.choice, Quot.sound].

Olean:

  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1938Direct312InequalityActual.olean
  bytes 296704
  SHA256 97026986C68A2B43EF61E70369BB4915DB2C0688C42CA0AE5F43061E9BDBB0FA
  mtime 2026-11-01T16:03:48+08:00 (source 16:02:35, olean newer)

Consumer probe:

  tmp/sheaf/xif/paper/_S1938ConsumerProbe.lean  EXIT=0, zero errors/warnings
  (imports the olean, prints the full signatures of S1938Target and 14 theorems, checks by example that the named target unfolds definitionally to
  -|log q| <= -average, applies the average <= 1 criterion, and re-prints the
  axiom sets; all [propext, Classical.choice, Quot.sound]).
  Log: tmp/sheaf/xif/paper/_S1938consumer.log (3628 bytes).

Consumer note: restating the inequality literally in another file needs the
local Fact (Irreducible (X^2 + 1 : Polynomial Q)) instance of the concrete
Gaussian field, as in S1487/S1880; this is recorded in the module docstring.

Upstream files: not modified (S1928, S1905, S1904, S1903, S1902, S1915, S1487,
OrigXiFPaperSignedHullActual unchanged).

## Boundary

- statement_compiles = true; proof_body_checked = true; kernel_closed = true
  (no sorryAx anywhere; all axiom probes clean); target_accepted is the
  coordinator's call -- this is a delegated package.
- No new hypothesis, object change, weakened quantifier, fake axiom, or
  circular interface is used.  The only inputs are S1928's closed form for the
  S1903 average, S1487's numerical evaluation of the actual q, and Mathlib
  finite arithmetic.
- Not run: full project build (lake build LeanFormal...), comparator
  acceptance, independent human review, coord/STATE.md and coord/queue.md
  updates (left to the coordinator).
