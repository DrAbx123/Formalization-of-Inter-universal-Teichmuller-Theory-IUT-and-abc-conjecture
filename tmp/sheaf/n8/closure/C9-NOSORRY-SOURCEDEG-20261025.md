# C9 no-sorry audit: SourceDegreeComparison

Task: task-480. Owner: multiradial. Date: 2026-10-25.
Scope: target tmp/sheaf/n8/closure/SourceDegreeComparison.lean only. No fake
proof, no axiom, no toy field. Deliverable: this file only.
target_accepted=false; C8/C1 open.

## 0. Verdict

SourceDegreeComparison.lean now COMPILES with lean-serial -j1 -R D:/lean,
EXIT 0. There is exactly one remaining declaration-level sorry:
sourceDegreeComparison. It is NOT provable from the existing declarations and
is false as stated for arbitrary independent C6/C7 data. The exact obstruction
is the missing Ob3-3 determinant/degree-realification donor already named in
C8DegreeActual and C8DetDonorSearch.

The baseline target did not compile: it used stale C7/SourceHolomorphicHull
types and missing C1/C2/C3/C5 imports. I repaired imports, section variables,
and the C7 parameter type to the actual current declarations; I did not replace
the theorem proof by a hypothesis, axiom, fake field, or toy type.

## 1. Target and compile result

File: tmp/sheaf/n8/closure/SourceDegreeComparison.lean
SHA256 6BA36657889C8A1F34F518A164D0151839C2A811AA2D233685B9AFCE5AAD3C4B
115 lines, 5356 bytes.

Compile:
  pwsh -NoProfile -File D:\lean\tmp\n8-20261018\lead\lean-serial.ps1
    env lean -j1 -R D:/lean tmp/sheaf/n8/closure/SourceDegreeComparison.lean

Result: EXIT 0. Warnings only: unused variable C6 in one definition, unused
C7 in c8HullLogVolume, and "declaration uses 'sorry'". No errors.

## 2. Exact declarations now used

Imports added:
  tmp.sheaf.n8.closure.C7Interface
  tmp.sheaf.n8.closure.C6ActualIQData

Actual project types/declarations used:
  - PaperNormalizedVolumeData, PaperLocalVolumeData, PaperLambdaData,
    PaperTupleWeightData (C6 paper weights/measure);
  - SourceInputBinding, SourceLogKummerData, SourcePilotRegionData,
    SourceAlgorithmCompatibilityData (actual C1/C2/C3/C5);
  - SourceHolomorphicHullData (actual current C7 record; fields iqHull_eq,
    image_subset_hull, contains_permitted, hull_subset_scaleShift,
    logVolume_lt_top, haar_pos, haar_lt_top, qPilot_mem);
  - C6ActualIQData (actual C6 IQ hull/log-volume/unit-reference data);
  - C6ProductVolumeData (C6/C6Prod handoff; used only as the old C6Prod
    parameter and not in the formula);
  - profileArithmeticDegree (production degree donor from
    HullDeterminantLogVolumeReduction).

C7 parameter type changed from the stale
  SourceHolomorphicHullData D C5 C6Prod n x
to the actual current
  SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
    (D := Dalg) (C5 := C5Alg) (mu := muIQ) (B := B) (T := T) n.
This is a source-declaration repair, not a new object.

Definitions:
  - c8RelativeDetDegree C6 =
      profileArithmeticDegree (M • (lambdaProfile - 0)),
    where M = C6.tupleWeights.denominator and lambdaProfile i = C6.lambdaData.lambda i.
  - c8HullLogVolume C6 C6Prod C7 =
      (1 / degree) * (Real.log (muIQ (commonHull muIQ B)).toReal -
        C6.localVolume.unitReferenceLog),
    where commonHull is the actual C7/C6 IQ hull B.hull and muIQ is the actual
    Haar measure on the IQ carrier.
  - sourceDegreeComparison states equality of the two definitions for all
    C6, C6Prod, C7 and is the sole sorry.

## 3. What is provable

The left-hand degree is provably the scalar product of the C6 tuple
denominator and the lambda sum:

  c8RelativeDetDegree C6 =
    (C6.tupleWeights.denominator : Real) *
      sum i, C6.lambdaData.lambda i.

This follows from profileArithmeticDegree_nsmul and
profileArithmeticDegree_eq_sum (both actual project lemmas). This is a
provable algebraic reduction; it is not the missing equality.

The right-hand c8HullLogVolume depends only on:
  - C6.localVolume.degree,
  - C6.localVolume.unitReferenceLog,
  - the IQ measure muIQ and the B/C7 common hull.
It does NOT depend on C6.lambdaData or C6.tupleWeights.

## 4. Exact obstruction

The theorem asserts, for arbitrary C6/C6Prod/C7:

  (M * sum lambda) = (1/degree) * (log muIQ(hull) - unitReference).

No field of PaperNormalizedVolumeData links lambdaData to localVolume.degree,
unitReferenceLog, or the C7 hull measure; lambdaData and localVolume are
independent fields. No field of SourceHolomorphicHullData links the hull
measure to C6 lambda weights. No project lemma computes muIQ(B.hull) in terms
of C6.lambdaData.

Consequently the equality is not derivable, and as an unconditional statement
for arbitrary independent C6/C7 data it is false. Definition-level
counterexample: hold C6Prod, C7, localVolume, tupleWeights and all C6 fields
except lambda fixed, and change lambda (e.g. multiply all lambda_i by 2 while
staying positive). The right-hand c8HullLogVolume is unchanged, while the
left-hand c8RelativeDetDegree doubles (unless the lambda sum is zero, excluded
by positivity). The claimed equality cannot hold for both choices. This is a
semantic counterexample, not a Lean instance; it shows why the remaining sorry
cannot be replaced by a proof from the current declarations.

The same obstruction is already recorded as named theorem-level sorries in:
  - C8DegreeActual.actualArithmeticDegree_eq_c8NormalizedLogVolume
    (actual arithmetic degree = actual C8 normalized log-volume); and
  - C8DetDonorSearch.c8Ob33SourceDonor_exists
    (the single missing Ob3-3 source identification).
The target's sourceDegreeComparison is exactly this missing Ob3-3
determinant-line-bundle/degree-realification donor; no such donor exists in
the production tree.

## 5. No fake/axiom/toy

No proof replacement was used:
  - no new axiom;
  - no new arbitrary Real parameter;
  - no fake C6/C7 data;
  - no hypothesis added to the theorem to make it trivially provable;
  - no det/tensor bookkeeping structure or toy Output/LogVol;
  - no other Lean source file was edited.
The actual project declarations are used; the C7 signature repair is the only
definitional change and is documented above. The one sorry is the exact
obstruction, not a hidden assumption.

## 6. Compilation and remaining gap

The file compiles with EXIT 0. The remaining warning is:
  declaration uses 'sorry'
at theorem sourceDegreeComparison (line 111). The target therefore is not
no-sorry; it is "no provable sorry replaced, exact unprovable sorry documented".
A no-sorry closure would require a new source theorem identifying the
determinant-degree profile with the C7 normalized hull log-volume (the Ob3-3
donor), or a corrected theorem with explicit source hypotheses. Neither is
introduced here.

Downstream caveat: N8Assembly.lean and SourcePilotApproximation.lean still use
the old C7 signature; they were not edited (out of scope for this task). The
target repair changes its C7 parameter type to the current actual C1-C7
declarations, so downstream integration must be updated separately. This is an
integration obstruction, not a fake proof.

## 7. Status

Target SourceDegreeComparison.lean: COMPILES, one documented sorry.
The remaining sorry is unprovable/false for arbitrary independent C6/C7 and is
exactly the Ob3-3 degree-realification gap. C8/C1 remain open.
No fake/axiom/toy; no mixed/E3; target_accepted=false.

## 8. Acceptance

Only SourceDegreeComparison.lean (target) and this MD were written. No other
Lean/Project source was edited beyond the target. The compile command above was
run with lean-serial -j1 -R D:/lean and returned EXIT 0. This file records the
exact declarations, repairs, and remaining obstruction. target_accepted=false.
