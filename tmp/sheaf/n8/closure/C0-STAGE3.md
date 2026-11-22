# C0-STAGE3 — audit and no-go for TargetSignature.N8TargetOutput

Status: C0Base.lean compiles exit 0 with no sorry.  The original C0 target
n8_targetOutput_nonempty is NOT proved; this record gives the exact no-go and a
corrected target boundary.

## 1. Audit of N8TargetOutput fields

N8TargetOutput (TargetSignature.lean) fields:

1. place : SourceInputBinding I.I
   Needs C1 SourceInputBinding: placeEquiv V ≃ NumberFieldPlaceIndex,
   selected v, SourceImageRealization selected, fiberMonEquiv.  None are
   constructed for arbitrary OriginalInput; C1 sourceInputBinding_nonempty is a
   named sorry, not a proof.  For arbitrary V there need not be an equivalence
   to the actual place index.

2. realization : SourceTheorem311Realization l Label Choice
   No constructor from OriginalInput.  The production realization assembly
   (SourceRealizationLifting.realization) starts from a large completed
   SourceRealizationLifting context, not from OriginalInput alone.  This field is
   therefore not inhabited by a production donor at C0.

3. hull_finite : forall n j, sourceHullVolume selected R n < top
   This is FALSE in general as a statement about the value-realized hull.  The
   production theorem
     sourceHullVolume_eq_top_of_degreeFaithful
   proves sourceHullVolume = top under pointwise degree faithfulness
     hdeg b : logDegreeAt 0 0 v (R.posRealAction (ofAdd b)) = b.
   Hence any output with a degree-faithful selected realization contradicts its
   own hull_finite.  C0 cannot assert unconditional finiteness of the value hull;
   the paper's finite hull needs the O-module/IQ structure or the compactness/
   hull-bound hypothesis, not the value-monoid sourceHullVolume.

4. hull_positive : forall n j, 0 < sourceHullVolume selected R n
   Not contradicted by hdeg (top is positive), but no unconditional proof from
   OriginalInput; it needs a nonempty positive-mass image/hull datum.

5. qPilot_mem_hull
   Conditional on a supplied R; the source theta-pilot point lies in
   sourceHolomorphicHull by the production membership theorem.  No R is
   constructed, so this is not available unconditionally.

6. q_le_theta
   No source theorem gives this for arbitrary I/R.  It requires the actual
   q/theta comparison (C9) and the source-to-IQ transfer; it is not a
   consequence of the current C0 fields.

Conclusion: N8TargetOutput is overstrong for arbitrary OriginalInput.  At
minimum, hull_finite must be removed/conditioned and place/realization must be
constructed or carried as explicit accepted data.

## 2. Exact no-go proved in C0Base.lean

File tmp/sheaf/n8/closure/C0Base.lean, compiled exit 0, no sorry.

Theorem 1:

    no_targetOutput_of_degreeFaithful
      (I : N8TargetInput l V Label Choice)
      (O : N8TargetOutput I)
      (hdeg : forall b,
        I.I.logDegreeAt 0 0 O.place.place.selected
          (O.place.place.selected_realization.posRealAction
            (Multiplicative.ofAdd b)) = b) : False

Proof: sourceHullVolume_eq_top_of_degreeFaithful gives top; O.hull_finite at
the zero pilot gives top < top, contradiction.

Theorem 2:

    no_targetOutput_of_no_sourceInputBinding
      (I : N8TargetInput l V Label Choice)
      (h : not (Nonempty (SourceInputBinding I.I))) :
      IsEmpty (N8TargetOutput I)

Proof: O.place would give the missing C1 binding.

These are exact no-go statements, not a construction of the original target.

## 3. Corrected target boundary

Corrected structure C0CorrectedOutput (C0Base.lean):

    place : SourceInputBinding I.I
    realization : SourceTheorem311Realization l Label Choice
    hull_bound : forall n, SourceHullLogBound I.I
      place.place.selected place.place.selected_realization n
    qPilot_mem_hull : forall n j, sourceThetaPilotPoint ... in sourceHolomorphicHull ...

where

    SourceHullLogBound I v R n :=
      exists C : Real, forall x : I.ThetaPilotPoint v,
        x in sourceHolomorphicHull v R n -> sourceLocalLogDegree v x <= C

This replaces the false unconditional hull_finite with the actual paper-shaped
hull compactness/log-degree bound.  The correct C0 theorem must either:

(a) take C1 SourceInputBinding and SourceTheorem311Realization as explicit
    accepted input/data, plus the SourceHullLogBound (paper compactness) and
    produce the corrected output; or
(b) work directly with the actual C7 IQ hull (C6ActualIQData /
    SourceHolomorphicHullData), whose positive finite IQ log-volume is a
    theorem-level obligation, and compare to C0 only afterward.

It must not assert sourceHullVolume < top for an arbitrary value realization.

## 4. Why n8_targetOutput_nonempty is not proved

- place: no C1 construction (placeEquiv/selected/R/fiberMonEquiv missing).
- realization: no OriginalInput -> SourceTheorem311Realization donor.
- hull_finite: no-go under degree faithfulness; needs O/IQ hull or compactness.
- hull_positive/qPilot_mem_hull/q_le_theta: require actual R and source-to-IQ
  comparison; not available.

No free field, True, empty card or new axiom was introduced.  C0Base.lean only
records the no-go and corrected boundary; it does not claim C0 closure.

## 5. Evidence

C0Base.lean:
- lines=99 bytes=4582
- SHA256 b56af6f850d8d7bd602bd7059032c66a27a9763cd5dd61bf503c10c2a9ab5f30
- lake env lean -R D:/lean exit 0
- no sorry

## 6. Next donor requests

1. C1: actual placeEquiv/selected/R/fiberMonEquiv donor (or prove the target
   only for inputs carrying a C1 binding).
2. SourceTheorem311Realization: an OriginalInput -> realization constructor.
3. SourceHullLogBound/compactness donor, or use C7 C6ActualIQData as the
   finite-volume carrier.
4. q/theta comparison from C9 actual IQ, not a free real.

Until then C0 remains no-go for the original target; the corrected target is
explicitly recorded and compiles.
