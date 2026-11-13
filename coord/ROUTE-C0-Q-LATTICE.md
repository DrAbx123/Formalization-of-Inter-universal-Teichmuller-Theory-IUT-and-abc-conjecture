# Route C0 — root-side q-lattice comparison

Date: 2026-11-13. Owner: stepxi. File:
tmp/sheaf/xif/paper/Mzk1RouteC0RootQLatticeActual.lean.
Status: CORE GREEN; theta-source normalization mismatch identified.

## Objects / theorems (no comparison input)

- `c0Alpha b := qrootElem T b` (actual 2l-th root of q);
- `c0QHat b := c0Alpha b ^ (2l)` with
  `c0QHat_eq_q : c0QHat b = algebraMap (rootBase b) (qVFamily b).q`;
- `c0Alpha_norm_le_one`, `c0Alpha_ne_zero`;
- unit-ball lattices `c0QLattice b = qhat_b * O_b`,
  `c0HLattice b = alpha_b * O_b`;
- `c0QLattice_subset_alpha : c0QLattice ⊆ c0HLattice`
  (uses alpha_b^(2l-1) integral);
- finite products `c0ProductQ ⊆ c0ProductH`;
- `c0ProductHaar_mono : haar(c0ProductQ) ≤ haar(c0ProductH)`;
- explicit remainder `c0Remainder = (2l-1) * Σ_b d_b * (-log||alpha_b||)`
  and `c0Remainder_nonneg`.

Build: DONE EXIT=0 2026-11-13T11:49:40.694Z (75s); olean 296648 B;
axioms [propext, Classical.choice, Quot.sound]; no sorryAx.

## §5.2 three checks

### ① q source
MATCHES.  `c0Alpha` is the actual root-system element (`qrootElem` from
`O2QrootGlueActual`) and `c0QHat` is proved equal to `algebraMap q` for the
actual `qVFamily` q.  No extra q normalization is inserted.

### ② theta source — FIRST MISMATCH
The current `c0HLattice` uses alpha_b = qroot (the label-1 theta value),
while the original theta image hull uses the coordinatewise MAXIMUM theta
value lambda_b = `rootThetaFieldLambda T b`.  Thus `c0ProductH` is not yet the
actual theta image hull; the correct H_root is
`rootExtensionProductFieldScaledHull T` (which equals
`rootExtensionProductImageHull T` by
`rootExtensionProductFieldScaledHull_eq_imageHull`).
The fix is available: `thetaOne_pow_norm_le_radius` gives
||qhat_b|| ≤ rootImageRadius_b = ||lambda_b||, hence
`c0QLattice b ⊆ rootThetaFieldLambdaO b`.  This substitution is not yet wired
into the C0 file; it is the first source-arrow mismatch.

### ③ normalization
PARTIAL.  The remainder currently uses d_b = finrank and -log||alpha_b||
(alpha = qroot), not the paper root radius r_b = rootImageRadius / lambda;
it also has no archimedean/infinite-place term.  Once ② is fixed, the
remainder should be rewritten with ||lambda_b|| and the same finite sum;
the archimedean/infinite part remains outside this finite bad-prime route.

## Conclusion

C0 has a green q-lattice inclusion and nonnegative finite remainder, but the
theta source (H_root = lambda_b O_b) is not yet wired.  Next step: replace
`c0HLattice` by `rootThetaFieldLambdaO`, prove the scalar inclusion via
`thetaOne_pow_norm_le_radius`, and re-run Haar comparison; no comparison
input is needed.

End of C0 report.
## V2: corrected theta source (GREEN)

File: tmp/sheaf/xif/paper/Mzk1RouteC0RootQLatticeV2Actual.lean.
DONE EXIT=0 2026-11-13T11:59:21.133Z (84s); olean 297216 B; axioms
[propext, Classical.choice, Quot.sound].

Changes:
- H_root replaced by `rootThetaFieldLambdaO T b` (lambda_b = coordinatewise
  maximum theta value); product H_root = rootExtensionProductFieldScaledHull
  = rootExtensionProductImageHull (actual theta image hull);
- `c0QLattice_subset_lambda` proved from `thetaOne_pow_norm_le_radius`
  (||qhat_b|| <= rootImageRadius_b = ||lambda_b||);
- `c0ProductQ_subset_imageHull` and `c0ProductHaar_le_imageHull`;
- `c0RemainderV2 = (2l-1) * sum_b d_b * (-log||lambda_b||)`, nonnegative.

§5.2 update:
- q source: MATCH (unchanged);
- theta source: FIXED in V2 (uses lambda_b, actual image hull);
- normalization: finite bad-prime part now uses r_b=||lambda_b||;
  archimedean/infinite-place terms are still a separate exact GAP (not claimed).

No comparison input in V1/V2.  V2 is the corrected C0 route; arch/infinite
normalization remains open.

End of V2 note.
## Arch / infinite-place normalization plan

Constructible pieces (already green):
- `Mzk1NormArchCKActual.archCK K = 1/[K:Q]`, `archCKToric K`;
- `hArc_eq_archCK_mul_sum : hArc K x = archCK K * sum_w hTerm K (infinite w) x`;
- `hNon_eq_archCK_mul_sum`; `hBox = hNon + hArc`;
- `Mzk1NormArchConsumerActual.hArc_nonneg_via_archCK` / `hNon_nonneg_via_archCK`;
- degree-one/ℚ forms in `Mzk1NormArchCHArcActual` (`hArc_rat`, etc.).

Can the arch term be constructed rather than named?
PARTIALLY.  Given an actual pair `(K, x)` (number field and global element), the
arch term `hArc K x` is a concrete function with explicit `archCK K`; no new
named arch factor is needed.  But C0 currently has no such pair: its objects
are root-extension unit-ball lattices over finite bad places, not a global
number-field element/idele, and there is no map

  (C0 root lattice / qhat_b) -> (K, x) -> hArc K x

in the tree.  Moreover C0's product is over finite bad places only; infinite
places of F are absent.  Therefore the arch **factor** is constructible, but
the arch **term coupled to the C0 measure comparison** is not: it needs a new
global finite-to-arch source arrow (global idele/element with prescribed
finite q_v valuations and its arch components).

Plan (minimal, no comparison input):
1. Set K := T.arithmetic.F (actual number field) and construct a candidate
   global element/idele from qVFamily; the q-family currently only gives local
   finite-place parameters, so this is the first blocked arrow.
2. If such x is constructed, define arch contribution `hArc K x` and use
   `hArc_eq_archCK_mul_sum`/nonneg lemmas; this replaces any named
   `archTerm` input.
3. Only then add `hArc K x` to the C0 finite bad-prime remainder and compare
   with the global height/readout; the missing identification is
   `log Haar(C0 lattice) + hArc K x = global height`, not the arch factor.
4. Degenerate check: for K=Q (D=1), archCK=1 and hArc is the unweighted
   infinite sum (`hArc_rat`); this constructs the factor but still does not
   create the C0-to-global arrow.

Status: finite bad-prime normalization is handled by c0RemainderV2;
arch/infinite normalization remains CONDITIONAL/GAP, with `archCK` explicit
but the global element/place arrow not constructed.

End of arch plan.
## Explicit finite + arch decomposition interface

File: tmp/sheaf/xif/paper/Mzk1RouteC0GlobalDecompositionActual.lean.
Status: GREEN (DONE 2026-11-13T12:20:08.592Z, 73s; olean 109736B; axioms
[propext, Classical.choice, Quot.sound]).

- `c0FiniteLog = log Haar(c0ProductQ)` (actual finite bad-prime C0 object);
- `c0ArchPart x = hArc K x` (actual IUT IV arch function, explicit
  `archCK K = 1/[K:Q]`; `c0ArchPart_eq_archCK` and `c0ArchPart_nonneg`);
- `C0GlobalDecomposition` has only a supplied `globalReadout` field plus
  equality `globalReadout = c0FiniteLog + c0ArchPart`.

Can the decomposition be constructed?  PARTIALLY: finite and arch parts are
actual/green; the global equality is NOT constructed because C0 has no global
readout type and no arrow from its finite root lattice to a global element x
with prescribed finite/arch components.  The structure is the precise
conditional interface, not a comparison.

End of decomposition note.
## Global readout: precise type and source task

The decomposition interface uses a bare `globalReadout : Real`.  The precise
actual candidate readout is the S3137 q-pilot reading

  qPilotLogVolumeReading (P : PaperQPilotObjectActual (l:=l) (I:=I)) : Real.

Required data to construct it from C0:
1. a global idele/element over `T.arithmetic.F` whose finite components at
   each lifted bad place equal `(qVFamily T b).q` (an element of the
   completion of F at `(nativeBadLift T).lift b`);
2. its archimedean components at `NumberField.InfinitePlace F`, matching the
   `hArc` term (or explicitly declared zero if the readout is finite-only);
3. a height/arithmetic-degree functional on that object whose log equals
   `qPilotLogVolumeReading P` (or the chosen global readout).

Can this be constructed from elements of `T.arithmetic.F`?
NO for a global element: `qVFamily` supplies local Tate parameters in
different completions; there is no theorem/choice of a global `x : F` whose
completion at every bad place is the given q_v.  A constant/known element of F
does not match the q_v valuations.
YES only for a finite-support **idele-like dependent function**: define its
finite component by `if v is a bad lift then (qVFamily ...).q else 1` and set
arch components to 1.  This is a legitimate dependent function, but it gives
no global element, no height identity, and its arch `hArc` is zero; it does
not produce `qPilotLogVolumeReading`.

Therefore the exact next source task is one of:
(A) prove existence of a global `x : T.arithmetic.F` with the prescribed
    completions (strong, not currently derivable), or
(B) construct an arithmetic-divisor/idele readout object plus a height
    functional and prove `readout = c0FiniteLog + c0ArchPart`; the local
    finite-support idele is constructible, but the height/readout identification
    and the qVFamily-to-divisor coefficient map are not.

The first missing arrow is `C0 finite q-lattice -> global idele/element`; the
second is `global object -> qPilotLogVolumeReading`.  Neither is a comparison
hypothesis; both are source-object gaps.

End of global readout note.
## Precise readout source type / next source task

Let `F := T.arithmetic.F` (actual number field).  A genuine readout source
would be one of the following.

(A) Global **element** `x : F` with prescribed finite components

  ∀ b : Bad (nativePlaceSelection T),
    algebraMap F (Completion ((nativeBadLift T).lift b)) x =
      (qVFamily T b).q.

Then `hArc F x` is the actual arch term (archCK explicit), and a global
height/readout can be built from the existing `hNon/hArc` functions.

(B) Global **idele-like** data

  finite : (v : NumberField.FinitePlace F) -> Completion v,
  finite_bad : ∀ b, finite ((nativeBadLift T).lift b) = (qVFamily T b).q,
  finite_good : ∀ v, (∀ b, v ≠ (nativeBadLift T).lift b) -> finite v = 1,
  arch : (w : NumberField.InfinitePlace F) -> (w.Completion)ˣ,
  globalLog : Real,
  readout_eq : globalLog = finiteLog + archLog.

Constructibility from `T.arithmetic.F` elements:
- (A) is NOT available.  qVFamily consists of local Tate parameters in
  different completions; there is no theorem/choice of a global x:F with the
  prescribed completions.  A constant or known element of F does not match
  the q_v valuations.  This is the first missing source arrow.
- (B) finite part IS constructible as a finite-support dependent function
  (`if v is a bad lift then qVFamily.q else 1`).  Arch units can be set to 1,
  but then `hArc` (which is defined for a global element, not arbitrary idele
  components) gives no arch term; there is no idele height functional tying
  this object to `qPilotLogVolumeReading`.

Thus even the constructed idele does not produce `globalReadout`; the exact
second missing arrow is an idele height/readout functional and its equality to
`qPilotLogVolumeReading`.  Neither arrow is a comparison assumption.

Next executable tasks:
1. (short) formalize the finite-support idele `C0GlobalIdele` with the bad
   components and good=1; this is constructible and checkable.
2. (hard) either prove (A) is impossible/needs new source, or build the idele
   height functional and prove `globalLog = c0FiniteLog + archPart`; neither
   exists in the tree.

End of readout source note.
## Source B idele construction status (definitional bad components)

File: tmp/sheaf/xif/paper/Mzk1C0GlobalIdeleActual.lean.
GREEN (DONE 2026-11-13T12:53:22.155Z, 66s; olean 149472 B; axioms
[propext, Classical.choice, Quot.sound]).

Replaced the failed total `if/choose` function by definitional component data:
- `c0BadSupport = univ.image lift` (finite support of bad lifts);
- `C0GlobalIdeleData` with
  `bad : ∀ b, Completion (lift b)`, `bad_eq : bad b = q_v`,
  `good : ∀ v, v ∉ c0BadSupport -> (Completion v)ˣ`, and
  `arch : ∀ w, (w.Completion)ˣ`;
- `c0GlobalIdeleData` constructed with
  `bad := fun b => (qVFamily T b).q`, `good := 1`, `arch := 1`;
- `c0GlobalIdeleData_bad` / `_bad_eq` are rfl; `_good_one` and `_arch_one`
  are rfl.

The dependent-cast total function is NOT needed for source B.  There is no
`c0FiniteBadConsistencyGap` anymore: bad components are definitional q_v.
(

Second missing arrow remains: `C0GlobalIdeleData` -> global height/readout;
no idele height functional and no `qPilotLogVolumeReading` equality.  The
finite bad data is fully constructed; only the readout bridge is open.

End of source B status.

## Idele height functional: constructible candidate vs readout gap

File: tmp/sheaf/xif/paper/Mzk1C0IdeleHeightActual.lean.
GREEN (DONE 2026-11-13T12:58:33.911Z, 63s; olean 76040 B; axioms
[propext, Classical.choice, Quot.sound]).

Constructed from `C0GlobalIdeleData`:
- `c0IdeleFiniteHeight D = heightWeight * sum_bad log max(norm q_v,1)`;
- `c0IdeleArchHeight D = heightWeight * sum_arch log max(norm arch_w,1)`;
- `c0IdeleHeight D = c0IdeleFiniteHeight D + c0IdeleArchHeight D`;
- `c0IdeleHeight_eq_finite_add_arch` (rfl);
- `c0IdeleHeight_eq_weight_mul_sum`: the same paper hBox shape
  `heightWeight * (sum_bad + sum_arch)`;
- finite/arch nonneg and total nonneg.

Relation to paper height:
The paper `hBox` is `heightWeight * (sum_finite hTerm + sum_arch hTerm)`
with `hTerm = log max(absValAt,1)` (ArithmeticDivisorDegree.lean:1220-1228).
Our candidate has exactly this sum shape, with local completion norms.  For a
global element `x : F`, equality would be rfl-level **given** the component
identifications

  D.bad b = algebraMap F (Completion (lift b)) x,
  D.arch w = algebraMap F (w.Completion) x  (as a unit),

and the second is only possible when the arch component is a unit (norm 1).
`C0GlobalIdeleData.arch` is a unit, so this is a real constraint, not a
definitional equality.

Exact readout gap:
  ideleReadout : C0GlobalIdeleData T -> Real,
  ideleReadout_eq : ideleReadout D = qPilotLogVolumeReading P
for an actual P, or = hBox F x for a global x whose components are D.
There is no such map/equality in the tree; this is the second missing arrow.

End of idele height note.
## C0 research conclusion (audit-ready, signed convention)

Actual constructions (all green):
1. q-lattice/measure (V1/V2): finite/arch;
2. definitional bad idele data: `C0GlobalIdeleData`;
3. candidate idele height: `c0IdeleHeight` (nonnegative finite+arch sums);
4. signed candidate: `c0SignedIdeleHeight = -c0IdeleHeight`;
5. conditional hBox equality: `c0IdeleHeight_eq_hBox_of_components`, and
   signed form `c0SignedIdeleHeight_eq_neg_hBox_of_components`.

Only missing source arrows:
1. `C0GlobalIdeleData` -> global element/idele readout (component
   identification);
2. readout -> actual `qPilotLogVolumeReading P` (S3137).

### Signed convention (important)

- `c0IdeleHeight D >= 0` is the unsigned height;
- `c0SignedIdeleHeight D := -c0IdeleHeight D` is the signed log-volume;
- S3137 `qPilotLogVolumeReading P = -|log q| <= 0`;
- therefore the consistent readout interfaces are
  `readout D = -hBox F x` (under component identification) and
  `readout D = qPilotLogVolumeReading P`.
  The earlier unsigned `readout D = hBox F x` is NOT used: it would conflict
  with the nonpositive q-pilot reading except at zero.

`C0ReadoutIdentification` (file Mzk1C0ReadoutIdentificationActual.lean)
GREEN DONE 2026-11-13T13:09:50.947Z (signed form, 60s; olean 101264 B);
records exactly the second arrow:
```
readout : C0GlobalIdeleData T -> Real
readout_eq_neg_hBox : C0HeightComponents T D x -> readout D = -hBox F x
readout_eq_qPilot : readout D = qPilotLogVolumeReading P
```
with no inhabitant constructed.

### Exact paper hBox component fields needed

paper definitions (ArithmeticDivisorDegree.lean:1171,1220-1228):
```
hTerm v x = log (max (absValAt F v x) 1)
hNon x = heightWeight * sum_{v in nonSupportFinset x} hTerm (finite v) x
hArc x = heightWeight * sum_w hTerm (infinite w) x
hBox x = hNon x + hArc x
```
Sufficient data fields for `C0HeightComponents T D x`:
1. `x : T.arithmetic.F`;
2. `finite_norm : forall b, norm (D.bad b) = adicAbv F ((nativeBadLift T).lift b) x`
   plus `nonSupportFinset x ⊆ c0BadSupport T`;
3. `arch_norm : forall w, norm ((D.arch w : w.Completion)) =
   absValAt F (infinite w) x`.
`C0HeightComponents` currently records the sum-level equalities
`finite_eq : c0IdeleFiniteHeight D = hNon x`,
`arch_eq : c0IdeleArchHeight D = hArc x`; these are the exact fields still
to be discharged from the norm/support data.

C0 route status: finite lattice/idele/height all actually constructed;
signed conditional hBox equality green; readout exact interface (signed)
written.  No comparison input, no axiom/sorry.

End of C0 conclusion.
