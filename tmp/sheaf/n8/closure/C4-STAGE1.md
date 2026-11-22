# C4 stage 1: source-witnessed output (revised)

## Template fields

- Task ID / group / owner / date: N8-C4 / group4 / multiradial / 2026-10-22.
- Goal node / SHEAF stage: C4 SourceWitnessedOutput / stage 1 (revised after audit).
- File: tmp/sheaf/n8/closure/C4-STAGE1.md (this file). No Lean file is written in
  this stage.
- Integration/build owner: C10 integration owner (not this stage); build not
  applicable to this document.
- Shared interfaces/conflicts: C0-STAGE1.md, C1, C3. No common definition
  changed. C4 does not use the discarded TargetSignature.lean trial.
- Continuation: after stage 1 acceptance, stage 2 or a named C0/C1/C3 child
  interface, not another generic C4 Lean variant.
- Acceptance: statement_compiles not applicable (no Lean declaration); proof
  body not checked; this record freezes objects/quantifiers/gaps.

## Correct input boundary after audit

C0-STAGE1.md freezes the allowed input as:

~~~text
l : PrimeGeFive
V : Type
I : OriginalInput l V
~~~

The earlier C4 draft incorrectly used N8TargetInput from
TargetSignature.lean:45. C0-STAGE1.md explicitly marks TargetSignature.lean as
a discarded trial; it is not a C4 statement dependency and is not used here.

The data v, R, n, j are NOT C0 input. They are produced inside the chain:

- C1 must produce/select v : V and the actual source realization
  R : I.SourceImageRealization v;
- C3 must produce n : ThetaPilotCarrier l and j : SignedLabel l.value as actual
  theta-pilot/source data.

C4 takes these C1/C3 outputs as its index/state data. It does not assume them as
C0 input and does not package them in a discarded structure.

## Actual index N, state X, output Y (candidate)

After C1/C3 have produced v, R, n, the actual source types used by C4 are:

~~~text
N := ThetaPilotCarrier l
X := I.ThetaPilotPoint v
Y := I.ThetaPilotPoint v
~~~

- ThetaPilotCarrier l is the actual theta-pilot procession carrier.
- ThetaPilotPoint v is the actual global value point carrier
  (ThetaPilotCarrier l x SignedLabel l.value) -> (I.primeStripAt 0 0).Mon v
  (SourceImageHull.lean:139). It is not Real.
- v and R are C1 data; n and j are C3 data. The type above is a candidate until
  C1/C3 fix those actual data.

G4 is the PRIMARY gap: ThetaPilotPoint v is only the value-point carrier, while
the paper's output data are F-prime-strip/region data. C4 cannot silently choose
ThetaPilotPoint v as the final output carrier. See G4 below.

## Actual C(I,n,x) and eval: candidate only

There is one currently definable actual choice family from the C1/C3 data: the
signed-label choice of the actual source theta packet.

~~~text
C_candidate (n : N) (x : X) : Type := SignedLabel l.value

eval_candidate (n : N) (x : X) (j : C_candidate n x) : Y :=
  I.sourceThetaPilotPoint v R n j
~~~

sourceThetaPilotPoint is SourceImageHull.lean:201, with application lemma
sourceThetaPilotPoint_apply (:205):
sourceThetaPilotPoint v R n j p = thetaImageValue R n j.

This is a CANDIDATE, not the final source-constrained C:
- it uses only the signed label;
- C_candidate does not depend on x;
- eval_candidate does not use x;
- it does not enforce the full same-source choice constraints, local/j-place
  relations, or Ind1/Ind2 constraints required by the paper.

The final C(I,n,x) must select actual source Choice values (from the chain-
produced SourceTheorem311Realization) and their constraints. Missing source
object: an actual map from the source Choice to the output carrier
ThetaPilotPoint v, plus the actual constraint predicate on choices. See G1.

No PUnit, True, arbitrary Nonempty, or free possibleImage field substitutes for
the missing full C.

## Output region U and witness

Once C/eval are fixed (candidate or final), define:

~~~text
U (n : N) (x : X) : Set Y :=
  {y | exists c : C n x, eval n x c = y}
~~~

Witnessed dependent pair:

~~~text
Witness (n x) := Sigma c : C n x, {y : Y // eval n x c = y}
~~~

Then:

- mem_U_iff: y in U n x iff exists c, eval n x c = y, by definition.
- U_eq_range: U n x = Set.range (fun w : Witness n x => w.2.1).
- The witness retains the actual source choice c; no numerical equality between
  different internal witnesses is assumed.

For the candidate, this is definitionally the actual source possible-image union
at n:

~~~text
U n x = {y | I.PossibleThetaPilotImageAt v R n y}
~~~

using PossibleThetaPilotImageAt (SourceImageHull.lean:225):
exists j : SignedLabel l.value, x = sourceThetaPilotPoint v R n j.

The free Profile.possibleImage field of the old kernel is NOT used: U is the
range of eval plus the dependent-pair witness. For the final C, this equality
must be restated only after G1/G4 are resolved.

## Ind1/Ind2 actual actions (candidate interface, actual action still missing)

Source-side actual actions exist on the source Choice carrier from the
chain-produced SourceTheorem311Realization:

- SourceTheorem311Realization.procession.ind1 : Label -> Choice -> Choice
- SourceTheorem311Realization.procession.ind2 : Label -> Choice -> Choice

with SourceLGPProcession/Core laws (one/add/inverse, commutation, level laws).
They are chain-produced, not C0 input.

C4 needs an actual map from the source Choice to ThetaPilotPoint v and actual
Ind1/Ind2 actions on that output, in order to state:

- ind1/ind2 group actions on Set Y;
- invariance/equivariance of U;
- the quotient relation if the paper takes one.

No such actual map/action exists in C0/C1/C3 or the inspected
SourceImageHull/SourceTheorem311Realization interface. The generic C4 skeleton's
ind1/ind2 : Label ->* Equiv.Perm Y is schema only. Exact gap G2.

## Ind3 inclusion/surjection directions (source directions exist on Real, not Y)

The actual source directions exist on the Real possible-image side:

- VerticalSiteData.nonarchimedean_inclusion:
  z in S -> z in nonarchimedeanImage m S (natural inclusion at v_Q in V_non).
- VerticalSiteData.archimedean_surjection:
  z in archimedeanImage m S -> exists y in S, z <= y (natural surjection at
  v_Q in V_arc).

These are fields of the actual Theorem311Source.Input/SourceVerticalRealization
used by SourceTheorem311Realization, and are exposed via VerticalSiteData
(SourceProcessionBoundary.lean:256 in the group4 record). They are NOT maps
Set (ThetaPilotPoint v) -> Set (ThetaPilotPoint v).

C2/C3 must supply the actual map from the output carrier to the local/global
Real possible-image carrier (or a directly corresponding local image map), plus
separate nonarchimedean inclusion and archimedean surjection operations on the
output regions with local v_Q indexing.

Until then, C4 records only the intended directions:
nonarchimedean S <= ind3_nonarch m S; archimedean ind3_arch m S <= S.
The generic skeleton's set operations are not asserted as actual. Exact gap G3.

## Precise volume compatibility (separate theorem)

The paper's precise compatibility of Kummer isomorphisms with respective
log-volumes is separate from both Ind3 directions (IUT III p.20-21 line 1150;
Proposition 3.9(iv)). C4 does not put a volume field into C or eval. The child
must provide:

- actual source/target log-volume functions on the relevant tensor-packet
  carriers;
- equality under the actual Kummer isomorphism, not merely the one-sided Ind3
  inclusion/surjection;
- a bridge to a Profile/logVolume readout only after the volume functions exist.

ThetaPilotPoint v is not itself a log-volume carrier, so this child is stated
after G4 fixes the output carrier. Exact gap G5.

## Source locations

- IUT III Corollary 3.12, text lines 10324-10352: definition of -|log(Theta)| as
  procession-normalized mono-analytic log-volume of the holomorphic hull of the
  union of possible images of the Theta-pilot object, relative to Kummer
  isomorphisms, subject to (Ind1),(Ind2),(Ind3); definition of -|log(q)| and the
  desired inequality.
- IUT III proof of Corollary 3.12, lines 10823-10898, especially (xi-d)-(xi-f):
  output data possibilities in the region U; log-Kummer correspondence in the
  1-column; R<= -|log(Theta)|; possible pilot-object log-volumes linked to
  -|log(q)|; approximation caveat.
- IUT III Remark 3.9.5, especially (i) holomorphic hull and (vii) (Ob3-3):
  determinants/log-volumes; C4 does not prove Ob3-3 and does not identify
  -|log(Theta)| with a free value.
- IUT III Theorem 3.11, (i)(ii): Ind1/Ind2/Ind3, Kummer correspondence and
  precise log-volume compatibility; group4-STAGE1.md line anchors
  :9324-:9456, :9458, :9613, :9786/9803/9817-9827/9843/9923.

## Statement dependencies (revised)

- C0-STAGE1.md: allowed input l : PrimeGeFive, V : Type, I : OriginalInput l V.
  C4 does not depend on TargetSignature.lean; that trial is discarded.
- C1: produces v : V and R : I.SourceImageRealization v as actual source data.
- C3: produces n : ThetaPilotCarrier l and j : SignedLabel l.value as actual
  theta-pilot/source data.
- C3/C2 donors: OriginalInput, ThetaPilotCarrier, SignedLabel, ThetaPilotPoint,
  sourceThetaPilotPoint, sourceThetaPilotImageAt, PossibleThetaPilotImageAt
  (SourceImageHull/SourceOriginalInput).
- SourceTheorem311Realization (SourceHodgeTheaterBridge:910): chain-produced
  Choice/procession/Ind data; used only after C2 produces it.

## Proof dependencies

- Definitions only for U/witness: no proof dependency beyond Sigma, Set.range.
- sourceThetaPilotPoint_apply and PossibleThetaPilotImageAt definition:
  SourceImageHull.lean:205, :225.
- Ind1/Ind2 group laws: SourceLGPProcession/Core laws once the actual output
  action is supplied; currently no output action.
- Ind3 directions: VerticalSiteData.nonarchimedean_inclusion,
  archimedean_surjection (source Real carrier), not transferable to Y without
  the missing map.
- Volume compatibility: no volume function on Y; separate C6/C7 dependency.

## Natural-language proof steps

1. Fix allowed C0 input l, V, I : OriginalInput l V.
2. Take the C1 data v : V and R : I.SourceImageRealization v; take the C3 data
   n : ThetaPilotCarrier l and j : SignedLabel l.value.
3. Set N = ThetaPilotCarrier l, X = Y = I.ThetaPilotPoint v.
4. Candidate: C_candidate n x = SignedLabel l.value and
   eval_candidate n x j = I.sourceThetaPilotPoint v R n j.
5. Define U n x as the existential image of eval; define the dependent-pair
   witness and prove U n x = Set.range witnessOutput.
6. For the candidate, prove U equals PossibleThetaPilotImageAt at n; this is
   definitional, not a new source assertion.
7. For full C: replace C_candidate by the actual source-choice family once C2/C3
   supply the actual map Choice -> ThetaPilotPoint v and the same-source
   constraint. Open (G1/G2).
8. For Ind1/Ind2: derive output actions from the actual source actions through
   the map of step 7; prove group-action/invariance laws. Open (G2).
9. For Ind3: split nonarchimedean inclusion and archimedean surjection; derive
   from VerticalSiteData through the actual Real-image map. Open (G3).
10. For output carrier: confirm whether ThetaPilotPoint v or a larger
    F-prime-strip/region carrier is the actual source output. Open (G4 primary).
11. For precise volume compatibility: prove equality under the Kummer
    isomorphism for actual tensor-packet log-volumes; separate theorem (G5).

## Reusable Mathlib / project donors

- Mathlib: Sigma/dependent pairs, Set.range, Set.image, Set.Subset, Equiv.Perm
  and MonoidHom action laws. No heavy analysis needed for witness/range.
- Project:
  - SourceImageHull.lean: ThetaPilotPoint, sourceThetaPilotPoint,
    sourceThetaPilotImageAt, PossibleThetaPilotImageAt.
  - SourceOriginalInput.lean: OriginalInput, ThetaPilotCarrier, SignedLabel,
    primeStripAt, Mon.
  - SourceHodgeTheaterBridge.lean: SourceTheorem311Realization and its
    SourceLGPProcession ind1/ind2/ind3, SourceEvaluationBridge.
  - SourceProcessionBoundary.lean: VerticalSiteData inclusion/surjection
    directions and Input.
  - group4-STAGE1.md section 2.5: old Profile ind3_upper/possibleImage mismatch;
    diagnosis only, not C4 construction.

## Exact gaps (revised; G4 primary)

G4 (PRIMARY). Output carrier: ThetaPilotPoint v is only the value-point carrier;
    the paper's output data are F-prime-strip/region data. Need C3/C1 to confirm
    the actual output carrier (or state precisely why ThetaPilotPoint v is the
    correct source output). Do not silently replace the final carrier by Real or
    by a smaller value-point type.
G1. Full constrained C: only the label candidate is currently defined. Missing:
    actual source Choice constraints and the map Choice -> ThetaPilotPoint v (or
    to the G4 carrier) that defines C(I,n,x).
G2. Ind1/Ind2 actual output actions: source actions exist on Choice only
    (SourceLGPProcession.ind1/ind2); no actual map to Y and no actual action on
    Set Y. Generic Equiv.Perm fields are schema only.
G3. Ind3 directions on Y: existing VerticalSiteData inclusion/surjection are on
    Real possible images; no actual Set Y -> Set Y nonarchimedean/archimedean
    operations with local v_Q indexing. Need C2/C3 map.
G5. Precise Kummer/log-volume compatibility: no actual volume functions on the
    output/Kummer carriers; separate child (C2/C6/C7), not implied by Ind3.
G6. C2/C3 actual Lean types: actual log-Kummer realization and actual q/theta
    source region are not yet available as green C2/C3 files; interfaces are
    named here, not assumed as proved.

Removed from this revision: the earlier N8TargetInput build-error gap. The
discarded TargetSignature.lean trial is not a C4 dependency.

## This package's decision and stop boundary

- This stage writes no Lean declaration and does not modify C0/C10 or any
  production file.
- The actual C/eval/U definition currently justified is only the label candidate
  above. The full source-constrained C and actual Ind operations are blocked on
  G4/G1-G3/G5, not replaced by arbitrary data.
- Stop after this stage-1 record; do not extend the generic Lean skeleton or
  invent C/Ind fields. The next executable action is a stage-1/2 child for the
  G4 output carrier and G1 choice map (C0/C1/C2/C3 owners), not another C4 Lean
  schema.

## Status fields

- statement_compiles: not applicable (this stage writes no Lean).
- proof_body_checked: not applicable / not run.
- kernel_closed: not applicable.
- target_accepted: not run.
- actual input: l : PrimeGeFive, V : Type, I : OriginalInput l V.
- actual output type candidate: I.ThetaPilotPoint v, with v/R from C1 and n/j
  from C3; G4 primary gap.
- actual C/eval: label-only candidate, defined in this record; full C missing
  (G1).

## Stage 2 implementation note (2026-10-22)

- tmp/sheaf/n8/closure/SourceWitnessedOutput.lean was updated to the actual C0 input
  OriginalInput, with C1PlaceData (v,R) and C3ThetaPilotData (n).
- Candidate Choice = SignedLabel, eval = sourceThetaPilotPoint, U = range of the Sigma
  witness; U_eq_range and U_eq_possibleImage are compiled.
- IndActionData is an explicit parameter obligation with real action/set types and
  inclusion/surjection direction laws; no actual source instantiation is asserted.
- lake env lean exit 0; file 176 lines, SHA256 66CF2235CED71AB7039826398D35D7B6D334C5B023DFAF2F8EAFE9D2679C388C; forbidden=0.
- Still open: actual C1/C3 data, actual IndActionData instantiation, full source-
  constrained C, and the G4 output carrier confirmation. No production edit.


## Label 结构更正（2026-10-23）

原文 labels 是 `S_{j+1}={0,...,j}` 的有限集合 + `Equiv.Perm` 对称（IUT III corpus 544-570），不是抽象 `Group Label`。C4 的 Ind1/Ind2 最终应使用 label set/permutation action；`C := SignedLabel l.value` 只是候选表示，不能把 group label 当原文。
