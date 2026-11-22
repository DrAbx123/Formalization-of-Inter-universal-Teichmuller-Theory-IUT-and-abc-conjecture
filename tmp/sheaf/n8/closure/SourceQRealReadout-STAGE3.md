# N8 C9 source q Real readout - stage 3 draft

- Task: independent source q-pilot Real readout and the source-q side of C9 actual_q_approximated.
- Owner: logdescent.
- Draft file: tmp/sheaf/n8/closure/SourceQRealReadout.lean.
- Compile status: lake env lean -j1 -R D:/lean EXIT=0 (one named sorry: the donor gap).
- Production edits: none. Stage-3 proof draft; no large build run in this goal round.
- Existing STAGE3.md is owned by C5; this file is the C9-specific record.

## Actual construction

The source q-parameter is C3 actual C3.q : FinitePlaceQCandidate C3.place.val
with C3.q.q_ne_zero.  The readout uses the actual CommonPrimeCompletion norm
and Real logarithm:

    sourceQNorm := norm (C3.q.q : CommonPrimeCompletion ...)
    sourceQLog := Real.log sourceQNorm
    sourceQSignedLog := -sourceQLog

sourceQNorm_pos and sourceQNorm_ne_zero follow from C3.q.q_ne_zero.
The C3 q-unit is identified with Units.mk0 C3.q.q C3.q.q_ne_zero; the T11
q-pilot point is identified with the C3 tensor landing C3.tensorLanding C3.q.q.

## Exact missing donor

The C8 IQ degree readout is not yet proved equal to the actual signed q norm:

    theorem sourceQRealReadout_eq_iqSignedHullLogAt
        ... (T : SourceThetaIQInterface (I := I) C3)
        (n : ThetaPilotCarrier l)
        (H : SourceHolomorphicHullData ... (T := T) n) :
        sourceQSignedLog C3 = iqSignedHullLogAt ... (T := T) (n := n) (H := H)

Named gap: the C6/C7 normalized IQ hull readout (iqSignedHullLogAt, equivalently
B.normalizedLogVolume / B.iqInterface.logVolume after normalization) has no
proved norm/valuation identity with -Real.log of the q norm.  The q parameter
is known to lie in the completion and to be nonzero; the missing bridge is the
actual arithmetic-degree / q-norm identity, not a free Real parameter.

## Source-q side of C9 actual_q_approximated

sourceQApproximated_to_iqDegree drafts the implication: if allowed values
approximate the actual source q readout,

    forall eps > 0, exists n y, y in Values and sourceQSignedLog C3 - eps <= y,

then, using the isolated donor identity above, the same values approximate
iqSignedHullLogAt ... (C7 n) and hence feed C9 actual_q_approximated once Values is
instantiated to C9IQ actual IQ values and C7 is the actual
SourceHolomorphicHullData family.

The proof step is exactly one rewrite by sourceQRealReadout_eq_iqSignedHullLogAt; no
other source construction is assumed.

## C9 integration boundary

C9 actual_q_approximated currently uses the C8 iqSignedHullLogAt readout as its q
value.  The source-q readout gives the independent actual q side:

- sourceQSignedLog is constructed only from C3 q + completion norm/log;
- T11 qPilotPoint is the C3 tensor landing of C3.q.q;
- the only missing link is the donor identity above.

Until that identity lands, C9 must not replace the q value by a free Real and
must not claim actual_q_approximated as closed.

## Status

- compiled exit0 in this fix round; only the donor-gap theorem has a named sorry;
- draft declarations are not acceptance evidence;
- sourceQRealReadout_eq_iqSignedHullLogAt is the exact named donor gap;
- no production file changed; existing STAGE3.md (C5 owner) untouched.
