# PaperN8RelaxedActual degeneracy audit (Wave33)

Date: 2026-10-24. Scope: audit only. No Lean source was modified.

Audited file: tmp/sheaf/n8/closure/PaperN8RelaxedActual.lean
(SHA 35B47C5F6642EBE4C293DE71D3D9DD0A1E01FBFDCDCB2C9D6141AF576F43F07D)
Underlying actual readout:
- P6RelaxedReadoutActual.relaxedFiniteReadout
- P6ArchReadoutActual.archReadout
- P6RelaxedGlobalNumerical.numericalGlobalReadout

## Verdict

The relaxed destination is NOT a real paper N8 destination. It is a formally
well-typed record whose entire numerical content collapses to zero. The
attached q <= Theta field is a native-q sign fact, not a comparison between the
q scalar and the actual global relaxed readout.

## Findings

### F1. globalReadout.value is exactly 0

P6RelaxedGlobalNumerical.numericalGlobalReadout constructs
  value := finite.value + arch.value.

P6RelaxedReadoutActual.relaxedFiniteReadout:
  reference v = unitSphereAt v
  region v = unitSphereAt v
  support = {badFinitePlace}
and value_eq uses relaxedFiniteEllOut. Every summand is
  weight v * ((log mu(region v)) - (log mu(reference v))) / dimension v = 0
because region = reference. Therefore finite.value = 0 for every support,
weight and dimension.

P6ArchReadoutActual.archReadout:
  support := empty
  value := archEllOut empty
and archEllOut is an empty Finset.sum, hence value = 0.

Consequently numericalGlobalReadout.value = 0 + 0 = 0.
This is definitional/arithmetic, not an extra hypothesis.

### F2. Values is {0}

PaperN8RelaxedActual.relaxedPaperN8OutputActual sets
  values := {G.value}
  values_eq := rfl
with G.value = 0 from F1. Therefore values = {0}. The claimed Values field is
not the actual source value family; it is the singleton of the already
zero numeric readout.

### F3. valuesBounded is vacuous

valuesBounded is proved by
  intro z hz
  simp only [Set.mem_singleton_iff] at hz
  exact le_of_eq hz
For values = {0} and theta = 0 this is z <= 0 after z = 0. It carries no
positive-mass/readout inequality and no source content. It would remain
vacuously true for any zero-value singleton.

### F4. q <= Theta is just native q <= 0

PaperN8RelaxedActual.q_eq says q = route.Q, and route.Q_eq_nativeScalar gives
  q = qPilotSignedLog X.
C9QPilotRegion.qPilotSignedLog_neg proves qPilotSignedLog X < 0.
Since theta = globalReadout.value = 0 from F1/F2, q <= theta is exactly
  qPilotSignedLog X <= 0,
which follows from qPilotSignedLog_neg alone and has no relation to the actual
global relaxed readout, its reference/region, its positive finite mass, or any
logdescent/transport comparison.

The named theorem relaxedPaperQLeTheta is therefore not an independent source
gap: it can be discharged from the native sign theorem, which makes the
degeneracy worse, not better. The name/sorry currently masks a trivial
inequality.

### F5. ValuesBounded and qLeTheta are not independent

Both are consequences of theta = 0 and values = {0}:
- valuesBounded is le_of_eq on a singleton;
- qLeTheta is qPilotSignedLog_neg.

Thus the exact-field target is formally inhabited but source-empty. It does not
establish Q/Theta/Values/Bounded/Q<=Theta for the paper objects.

## Decisive correction

The destination must be rebuilt with a nondegenerate readout and a contentful
Q <= Theta. The following are required, not optional:

1. Nondegenerate global readout value.
   Use a reference/region pair with reference != region on the actual
   positive-finite-mass regions, and a nonempty archimedean numerical support,
   so that the actual ell_out value is not identically zero. Add and prove
     globalReadout.value != 0
   as a target guard. The current finite sphere reference = region and the
   archimedean empty support must not be reused as the destination readout.

2. Non-singleton source Values.
   Values must be the actual readout/source value family (for example the
   actual source hull/region volume images), not {globalReadout.value}. The
   singleton construction collapses ValuesBounded to reflexivity and must be
   removed from the destination.

3. Actual Q <= Theta.
   Q <= Theta must be derived from the actual logdescent/transport comparison
   between the native q scalar and the nondegenerate global relaxed readout.
   It must not be derived from qPilotSignedLog_neg with theta = 0, and it must
   not remain a named source gap that is actually a sign fact.

4. Nondegeneracy audit obligation.
   The corrected target should contain explicit guard propositions
     globalReadout.value != 0
     values != {0}
   (or exact equivalents) so that a zero-collapse record cannot satisfy the
   destination again.

## Minimal file-level action

- Do not accept PaperN8RelaxedActual.RelaxedPaperN8Output as the paper N8
  destination.
- Keep it only as a formal record/negative control demonstrating the collapse.
- Rebuild the destination on P6RelaxedGlobalReadoutActual with a nonzero
  reference-relative readout and a source Values family; prove q <= Theta from
  the transport comparison, not from qPilotSignedLog_neg.
- Until then, report the current target as formally compiled but
  source-degenerate/not accepted.

## Evidence index

- tmp/sheaf/n8/closure/P6RelaxedReadoutActual.lean:
  relaxedFiniteReadout: unitSphereAt reference = region; relaxedFiniteEllOut.
- tmp/sheaf/n8/closure/P6ArchReadoutActual.lean:
  archReadout support := empty; archEllOut support.sum; value = archEllOut empty.
- tmp/sheaf/n8/closure/P6RelaxedGlobalNumerical.lean:
  value := finite.value + arch.value; value_eq.
- tmp/sheaf/n8/closure/PaperN8RelaxedActual.lean:
  theta_eq, values_eq, valuesBounded, q_eq, relaxedPaperQLeTheta.
- tmp/sheaf/n8/closure/C9QPilotRegion.lean:
  qPilotSignedLog_neg.

No Lean compiler run is claimed for this audit; the facts above are definitional
reads of the cited files plus the already compiled destination.
