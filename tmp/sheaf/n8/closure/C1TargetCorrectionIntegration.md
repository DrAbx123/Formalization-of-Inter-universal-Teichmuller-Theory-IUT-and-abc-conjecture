# C1 target correction integration (Wave13)

Updated: 2026-10-24.  Documentation/DAG recommendation only; no Lean file was
edited.  Scope: C1 fiber-monoid target in the current N8 paper route.

## 1. Old target: rejected

Target (old):

  C1FiberMonEquivData.fiberMonEquiv
    : forall n m v,
        (I.primeStripAt n m).Mon v ≃*
          SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v)

Source: tmp/sheaf/n8/closure/C1FiberMonEquivAttempt.lean.
Current status: named sorry c1FiberMonEquivData_nonempty; do NOT treat as a
satisfiable target or closure evidence.

No-go (actual, zero sorry):
tmp/sheaf/n8/closure/C1FiberMonTargetNoGo.lean, lines 136,
SHA256 c2f7088a15ee9ce229c1f8d2a13c50cadce65d78cc4416a9726720f8b3ce4ce9.

If the old strip Mon at a place is the actual unit monoid PlaceUnitMonoid
(units of the local completion):

- finite branch: units contain -1 of order 2; finitePlaceValueGroup =
  Multiplicative Z is torsion-free;
- infinite branch: units contain -1 of order 2; archimedeanValueGroup =
  Multiplicative R is torsion-free.

Thus no MulEquiv PlaceUnitMonoid -> SourcePlaceValueGroup exists at either
branch, and no_c1FiberMonEquivData_of_monEquivPlaceUnit proves the full-unit
C1FiberMonEquivDataExists target false under that identification.

Important scope: the no-go is conditional on the old-strip-to-PlaceUnitMonoid
identification.  For arbitrary old I.primeStripAt Mon (not identified with the
canonical unit monoid) the no-go is not automatically transferable; that
identification is itself the missing donor.

## 2. Corrected target: quotient by kernel

C1PlaceValueGroupActual.lean already constructs the actual quotient comparison:

  PlaceUnitMonoid (F := F) P ⧸ placeUnitKernel (F := F) P
    ≃* SourcePlaceValueGroup (F := F) P

via placeUnitQuotientEquivValueGroup (finite: quotient by integral units;
infinite: quotient by the norm-one subgroup/kernel of infiniteUnitToValueGroup).

C1FiberMonTargetNoGo.placeUnitQuotient_target_actual proves the quotient
equivalence is actual at every finite/infinite place.

Corrected C1 target should therefore be the quotient-by-kernel comparison,
not the full-unit equivalence.  Schematic corrected target (not Lean-edited):

  CorrectedC1FiberMonData I e where
    selected : V
    selected_realization : I.SourceImageRealization selected
    stripUnitIdentification :
      forall n m v,
        Nonempty ((I.primeStripAt n m).Mon v ≃*
          PlaceUnitMonoid (F := I.initial.arithmetic.Fmod) (e v))
    fiberMonQuotEquiv :
      forall n m v,
        Nonempty (((I.primeStripAt n m).Mon v) ⧸ transportedKernel
          ≃* SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v))

where transportedKernel is the integral-units/norm-one kernel transported along
stripUnitIdentification.  The quotient equivalence itself is actual at the
PlaceUnitMonoid level; the remaining missing object is the old-strip unit
identification (and its transported kernel), not a new value-group iso.

## 3. What is missing

1. Old-strip-to-PlaceUnitMonoid identification:
   forall n m v, Nonempty ((I.primeStripAt n m).Mon v ≃* PlaceUnitMonoid ...).
   No production declaration supplies it.
2. Selected place and SourceImageRealization selected (C1-d).
3. Transport of the integral-units/norm-one kernel along that identification.
4. The quotient comparison can then be transported to the old strip.

No arbitrary equivalence should be introduced for 1 or 3.

## 4. DAG recommendation

Current DAG nodes touching C1:
- n8-c1-source-input-binding (statement_compiles, named sorry
  sourceInputBinding_nonempty)
- n8-s3-c1 (proof_leaf, stage3 in_progress, target_not_frozen)

Recommended edits (record only; no JSON edit in this wave):

1. Mark the old full-unit target as rejected:
   - node n8-s3-c1: semantic_status = target_corrected_quotient_required;
   - target field C1FiberMonEquivData: target_rejected_full_unit_no_go;
   - do not count c1FiberMonEquivData_nonempty as a valid named-sorry target.

2. Add child node n8-s3-c1-quotient:
   kind target; parent n8-s3-c1;
   statement: corrected quotient-by-kernel C1 fiber comparison plus old-strip
   unit identification;
   proof_status: statement_pending;
   gaps: old-strip Mon ≃* PlaceUnitMonoid; transported kernel; selected R;
   consumers: C1 binding, C2/C3/C7 native bridges;
   evidence: C1FiberMonTargetNoGo.lean (no-go), C1PlaceValueGroupActual.lean
   (actual quotient equivalence).

3. Keep n8-c1-source-input-binding status honest:
   statement_compiles + named sorry, but its fiberMonEquiv field is the old
   full-unit target; annotate that the field must be replaced by the corrected
   quotient target.  Do not mark target_accepted.

4. C1 record cross-references:
   - C1-STAGE1.md: add correction pointer to this file and to
     C1FiberMonTargetNoGo.lean.
   - C1-STAGE3.md: replace the old fiberMonEquiv target with the quotient
     target, keep old no-go as evidence.
   - C1FiberMonEquivAttempt.lean: do not delete history; mark the old
     c1FiberMonEquivData_nonempty as superseded (documentation/DAG status, no
     Lean edit in this wave).

## 5. Status

Old C1 full-unit target is no longer admissible.  Corrected target is
quotient-by-kernel; its quotient equivalence is actual, but the old-strip unit
identification and transported kernel are missing.  No target_accepted,
kernel_closed, or Paper N8 closure claim.  ABC/old layer excluded.
