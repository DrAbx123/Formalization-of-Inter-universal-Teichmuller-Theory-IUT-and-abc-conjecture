# N8 P4/P5 anchor bridge + label status

Date: 2026-11-06.

## LabelData status ACTUAL

LabelData.lean exists, olean=true, size=125872, src SHA256=23BB89E89533B99F3F365C1A0BB5ED7143EEB4B19855C707C3550BF6C2FF5355

Definitions: LabelData (Labels, Fintype, Equiv.Perm), ProcessionLabelData (card_eq level+1), C0ProductionAdditiveIndex, C0AdditiveLabelTransport (indexEquiv only).

This is the paper-correct object: finite set + permutation, not Group.

## SourceWitnessedOutput status

Header still says PENDING LABEL CORRECTION: [Group Label] is provisional.

Actual declarations use [Group Label]: IndActionData ind1/ind2 monoid homs, Choice, eval (= sourceThetaPilotPoint), U (range of eval), Witness, witnessOutput, witnessOutput_eq_eval, mem_U_iff, U_eq_range, U_eq_possibleImage.

## P4/P5 anchor bridge skeleton

Add P4P5LabelAnchor with labelData : LabelData, anchor : labelData.Labels -> SignedLabel l.value, anchor_surj.
Add P4P5AnchorBridge with anchor and eval_eq plus U_eq.
Route: replace Group Label by LabelData.Labels; eval unchanged; U equals range anchor by U_eq_range.

## Exact remaining

1. Replace provisional Group Label or add parallel non-Group version.
2. Prove anchor_surj from U_eq_range.
3. P4/P5 consumers still use Group Label and need transport.

## Caveat

SourceWitnessedOutput is sorry-free but still carries the pending label correction. LabelData is the landed paper object.

