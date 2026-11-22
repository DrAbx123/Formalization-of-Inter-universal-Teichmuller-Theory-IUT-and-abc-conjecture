# C9 no-sorry audit of C9Proof.lean

Task ID: task-484 / C9-NOSORRY-C9PROOF-20261025. Owner: primespine. Date: 2026-10-25.
Target: tmp/sheaf/n8/closure/C9Proof.lean.
Lean hash: SHA256 a0f39f2e52eed9fea4394a99db409a34aca38d417d50c9fa69cb001c867915c0, 11311 bytes, 249 lines.
Compile: `lean-serial env lean -j1 -R D:/lean tmp/sheaf/n8/closure/C9Proof.lean` -> exit 0, no warnings.
No fake, axiom, toy field, or arbitrary carrier was added.

## 0. Result

**C9Proof.lean is now sorry-free and compiles.** The original file contained 7 literal `sorry` occurrences: 4 executable tactic sorries and 3 docstring mentions. None of the 4 was an unconditionally provable target in the current source: they asserted directions opposite to the production donors or required unproved source conditions. They were replaced by explicit conditional hypotheses plus proved obstruction theorems, not by fake proofs. The exact obstructions are recorded below.

This does **not** prove C9/Cor3.12. It makes the file honest and sorry-free while preserving the no-go content.

## 1. Audit of the 7 occurrences

| # | original occurrence | kind | action |
|---|---|---|---|
| 1 | `thetaQ_lt_one_obligation` (line 115) | tactic sorry | replaced by conditional `sourceImageLogDegree_nonpos_of_q_lt_one` taking `q<1` |
| 2 | `sourceScalingUnits_nonpos_obligation` (line 133) | tactic sorry | replaced by explicit scaling hypothesis; obstruction theorem added |
| 3 | `missingSourceQHullComparison_attempt` (line 160) | tactic sorry | replaced by conditional `missingSourceQHullComparison_of_hyp`; obstruction added |
| 4 | `missingValuesBoundedByTheta_attempt` (line 165) | tactic sorry | replaced by conditional `missingValuesBoundedByTheta_of_hyp`; obstruction added |
| 5 | docstring 'Named sorry: q is contracted' (line 112) | doc mention | removed/reworded |
| 6 | docstring 'Named sorry: hull scalings' (line 129) | doc mention | removed/reworded |
| 7 | docstring 'Named sorry for the exact (xi-d)' (line 148) | doc mention | removed/reworded |

At the literal level, `grep` finds 0 `sorry` and 0 `axiom` in the final file.

## 2. Why each tactic sorry was not unconditionally provable

### 2.1 `thetaQ_lt_one_obligation`

Target: `(I.theaterAt (n.val) 0).thetaPacket.q < 1` for every procession.

Exact obstruction:

- `FiniteThetaPacket` supplies only `q_pos : 0 < q`; no theorem gives `q < 1`, `q <= 1`, or a bound on the q-parameter.
- The source packet q is an arbitrary positive Real; positivity does not imply contraction.
- For the C9 b=273 Tate profile the q-parameter is a large positive period, not < 1; no source theorem supplies the contraction needed by this route.
- The file now takes `q < 1` as an explicit hypothesis in `sourceImageLogDegree_nonpos_of_q_lt_one`. It does not prove the hypothesis.

### 2.2 `sourceScalingUnits_nonpos_obligation`

Target: every scaling unit has `sourceLocalLogDegree <= 0`.

Exact obstruction: this is **refuted** under pointwise degree faithfulness by the existing production theorem

    `not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful`

(`SourceContractionWlogReduction.lean`). The constant scaling of exponent 1 lies in `sourceScalingUnits` and has positive log-degree, the index cardinality. Hence the scaling hypothesis cannot be proved from the current source; it is a named ambient compactness/O-module input. The file now takes it as an explicit hypothesis and records the negation theorem `not_sourceScalingUnits_nonpos_of_degreeFaithful`.

### 2.3 `missingSourceQHullComparison_attempt`

Target: `QSigned n <= ThetaSigned n` for every n.

Exact obstruction:

- The production direction is the reverse: `ThetaSigned n <= QSigned n` (hull contained in the image-union), proved as `thetaSigned_le_qSigned`.
- `QSigned <= ThetaSigned` is equivalent, under finiteness, to `sourceHullVolume <= sourceSetVolume` (the (xi-d) hull/image comparison); the file proves this equivalence.
- That comparison is equivalent to the absence of a positive-degree point in the hull; if `1 < q`, the target is **false** (`not_missingSourceQHullComparison_of_one_lt_q`), by the existing countertheorem `not_sourceHullVolume_le_imageVolume_of_one_lt_q`.
- No source equality or reverse comparison is available. The file keeps only the conditional `missingSourceQHullComparison_of_hyp`.

### 2.4 `missingValuesBoundedByTheta_attempt`

Target: every actual signed output value `z` satisfies `z <= ThetaSigned`.

Exact obstruction:

- The production pointwise direction is the reverse: `ThetaSigned <= z` for every image value `z` (`thetaSigned_le_signed_value`).
- The image point lies in the hull, so the hull volume is at least the point volume; taking negative logs gives `ThetaSigned <= z`. Hence `values <= Theta` is the opposite inequality and is not derivable.
- The file now keeps only the conditional `missingValuesBoundedByTheta_of_hyp`.

## 3. What was proved and retained

- `thetaSigned_le_qSigned`: production reverse signed comparison, unchanged.
- `thetaSigned_le_signed_value`: pointwise reverse value bound, unchanged.
- `qSigned_le_thetaSigned_iff_hullVolume_le_imageVolume`: exact equivalence of the C9 direction with the hull/image comparison under finiteness.
- `sourceHullVolumeLeImageObligation_iff_no_pos`: equivalence of the hull/image comparison with absence of positive hull degree.
- `sourceImageLogDegree_nonpos_of_q_lt_one`: conditional image-side nonpositivity.
- `sourceNoPositiveHullDegree_of_contracted`: conditional no-positive-hull-degree.
- `sourceHullVolumeLeImageObligation_of_contracted`: conditional hull/image comparison.
- `sourceHullVolumeLeImageObligation_of_q_le_one_and_scaling`: conditional from q<=1 and scaling nonpositivity.
- `not_sourceHullVolumeLeImageObligation_of_one_lt_q`: exact counterexample direction for q>1.
- `exists_pos_sourceHullDegree_of_one_lt_q`: positive hull-degree witness for q>1.
- `not_sourceNoPositiveHullDegree_of_one_lt_q`: negation of the finite-phase target for q>1.
- `not_sourceScalingUnits_nonpos_of_degreeFaithful`: source-level refutation of the scaling hypothesis.
- `missingSourceQHullComparison_of_hyp`, `missingValuesBoundedByTheta_of_hyp`: honest conditional forms.

## 4. Compile

Command:

    lean-serial env lean -j1 -R D:/lean tmp/sheaf/n8/closure/C9Proof.lean

Result: exit code 0; no warnings; no `sorry`/`axiom` in the final file.

## 5. Scope and exact residual obstruction

The file is sorry-free but **not a proof of C9**. Its exact residual obstruction is:

1. q-contraction `q < 1` is not a source theorem; the 2l-root/native q data only give positivity.
2. Scaling nonpositivity is refuted under degree faithfulness and remains an ambient O-module/compactness input; no source proof.
3. The C9 q/hull direction is the reverse of the production hull-containment direction; the missing object is the (xi-d) hull/image equality/comparison (equivalently, no positive hull degree).
4. The value bound `values <= Theta` is the opposite of the proved pointwise `Theta <= value`.

No fake, axiom, toy field, or arbitrary carrier was introduced. Conditional hypotheses are explicit and named. The imported `C9Native` module still contains two separate named obligation sorries; they are outside the target file and are not used as proofs here. The target C9Proof itself is sorry-free.

target_accepted=false; kernel_closed=false.
