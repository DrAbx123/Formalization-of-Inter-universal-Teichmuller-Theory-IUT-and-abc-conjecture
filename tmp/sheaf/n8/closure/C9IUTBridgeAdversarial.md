# C9 adversarial integration review of the IUT bridge files

Task ID: task-476 / C9IUTBridgeAdversarial.md. Reviewer: primespine. Date: 2026-10-25.
Object: C9IUTBridgeProbe.lean and the bridge/consumer modules it checks.
Scope: adversarial integration review; actual project declarations only; no toy-field acceptance; no Lean/Project edits; only this file written.

## 0. Verdict

**REJECT the bridge as an integration proof of Cor3.12/C1.** The probe only `#check`s declarations; it proves no composed theorem. The consumer layers it checks contain arbitrary q/theta/target/h fields and assume the comparison inequalities rather than deriving them from the source. Several modules are explicitly finite/normed models, not realizations of the IUT source carrier. There is no hidden C1 in the probe itself, but the integration is not established: the actual declarations are interfaces with open source cards.

Per-file verdicts below.

## 1. `C9IUTBridgeProbe.lean` (27 lines): ACCEPT only as a compile probe; REJECT as bridge proof

The file imports six actual project modules and contains only `#check` commands (lines 12-27). It contains no theorem, no structure, no axiom, and no `sorry`.

- Accept: it is a useful declaration-existence/compile probe.
- Reject as integration: `#check` does not compose the declarations, does not prove `Cor312Conclusion` or C1, and does not verify the semantic source mapping. A successful probe would only show the names exist and elaborate.

## 2. `SourceTheorem311ReferenceContract.lean` (534 lines): ACCEPT as actual source-facing contract; NOT a C1 bridge

The module imports the actual Theorem3.11 assembly and defines `SourceTheorem311ReferenceOutput`, a large record with actual fields `partI/partII/partIII`, quotient/volume/Ind data, Proposition3.9 data, etc. It is not a toy type: it is built over `SourceP1P2Bundle` and actual `OriginalInput`.

However:

- It is an output contract conditional on a `SourceP1P2Bundle`; it does not construct that bundle or assert its existence.
- It has no q-pilot membership field and no `Q_can/h_can`; it does not prove C1/Cor3.12.
- The contract fields are numerous and mostly source-facing; no toy q/h fields were found in this file.

Verdict: ACCEPT as a project declaration/contract; REJECT as a bridge to P6/C1. The contract's existence does not close the source construction.

## 3. `ContractSourceReduction.lean` (452 lines): REJECT as a source proof; ACCEPT only conditional algebraic constructors

This module is the central bridge and the main problem. It constructs `StepXIFiniteCertificate` values from a hull and real scalars:

    qSigned thetaSigned : Real,
    q_le_hull : qSigned <= hull.hullVolume,
    hull_le_theta : hull.hullVolume <= thetaSigned,
    q_negative : qSigned < 0.                                           (3.1)

and `finiteLinkEvidenceOfHullTarget` sets `targetSigned := hull.hullVolume`, so `q_le_target` is the assumed `q_le_hull` field. This is not a derivation of the source comparison; it is an input surface.

Hidden/toy fields:

1. **Arbitrary q.** `qSigned` is an arbitrary real in `ofHullWeights`/`ofHullUniform`. In `ofAbsoluteDegreeNormalizedSignedLog` it is instantiated by `absoluteDegreeNormalizedLowerSignedLog`, but the file header explicitly says: 'The identification of this quantity with the paper's actual q-pilot is NOT asserted.' So it is not `Q_can`.
2. **Arbitrary theta.** `thetaSigned` is arbitrary; no identification with the paper's `h_can=-|log Theta|`.
3. **Arbitrary target.** `finiteLinkEvidenceOfHullTarget` chooses the target to be the hull volume by definition, making the comparison fields tautological. This is a hidden target choice, not source-derived.
4. **Comparison assumed.** `q_le_hull` is a field. For the hull-target link it becomes the desired q-comparison; the proof does not derive it.
5. **Hull is a model.** The `FiniteHull` here is the finite positive-packet model from `Volume.lean`, not the actual IQ holomorphic hull.

The algebraic constructors are internally valid conditional lemmas; the module does not construct a paper certificate. The header's 'not proved here: IPL/SHE/APT content, amplitude bound, source-facing hull log-volume' confirms the source cards remain open.

Verdict: REJECT as a source/Cor3.12 bridge; ACCEPT the conditional constructor algebra with its assumptions explicitly listed.

## 4. `ParametricStepXI.lean` (382 lines): REJECT as a C1 bridge; toy q/h fields

`StepXIInput` fields (lines 27-42) include:

    qSigned targetSigned thetaSigned : Real
    q_negative : qSigned < 0
    ipl she apt : Prop
    ipl_evidence : ipl ...
    q_le_target : qSigned <= targetSigned
    target_le_theta : targetSigned <= thetaSigned.                         (4.1)

The output part is actual (`output := runAlgorithm carrier input`), but q/target/theta and both comparison inequalities are arbitrary inputs. `StepXIInput.toContract` just repackages them; `StepXIInput.conclusion` applies `cor312_of_constructed_stepXI` to the contract. This is a conditional schema, not a source proof.

There is no identification of `qSigned` with the paper q-pilot, `targetSigned` with the source target, or `thetaSigned` with the paper hull. The three Ind routes and wall certificate are actual project declarations, but they do not supply the q/h comparisons.

Verdict: REJECT as C1/Cor3.12 bridge; ACCEPT only as an interface with explicitly arbitrary q/h fields.

## 5. `SourceHullInterfaceDischarge.lean` (284 lines): ACCEPT its obstructions; REJECT as a source discharge

The module is honest: it says the actual source realization remains open.

- (F1) proves a **normed-space Haar-contraction consistency model** of `IQHullLogVolumeInterface`; this is a model, not the IUT carrier.
- (F2) proves under pointwise degree faithfulness that the value-level source hull volume is `⊤` and the paper-shaped compactness input is unsatisfiable.
- (F3) gives real-valued packaging of a finite hull log-volume.
The header explicitly states: 'Nothing here is claimed about the actual IQ carrier'; the discharge remains open by `iqHullInterfaceDischarge`.

Verdict: ACCEPT F1-F3 as model/obstruction/transfer lemmas; REJECT any claim that the source hull interface is discharged. The source hull/finiteness card remains open.

## 6. `SourceQSideComparison.lean` (216 lines): ACCEPT local q-side lemmas; REJECT as paper q-pilot comparison

The module proves actual theta-value comparisons:

- `sourceSetVolume_possibleImage_eq_iSup_sourceQSide` and single-label lower bounds;
- `sourceQSideNormalizedValue` defined from actual `thetaValueAt`;
- `iqHullCertificate_hqSlot_of_neg`: the ENNReal hq slot is degenerate for q<0 (it sees only 0≤0).

However:

- `q` in the consumer comparison is an arbitrary real; the file explicitly says a paper-faithful signed q carrier and the genuine q comparison are not proved; they are named hypotheses.
- The source hull volume is `⊤` under degree faithfulness, so the theta upper-bound slot is not satisfiable at this realization level.
- No `Q_can=-|log q|` object or C1 output is constructed.

Verdict: ACCEPT the local theta/q-side algebraic facts and the degeneracy warning; REJECT as a paper q-pilot/C1 bridge.

## 7. `Volume.lean` (189 lines): ACCEPT algebraic packet identities; REJECT as source hull

The file is explicitly a finite model: 'The paper's holomorphic hull and determinant/tensor normalization are not constructed here... a proved model layer, not an IUT existence theorem.'

`FiniteHull` has arbitrary `volume : label -> Real`, `hullVolume : Real`, and `contains`; `StepXIFiniteCertificate` has arbitrary `qSigned`, `thetaSigned`, and comparison fields. The determinant/tensor/rescaling identities are correct algebra, but no actual IQ hull or source log-volume.

Verdict: ACCEPT packet/determinant algebra; REJECT as the paper's hull/C1 construction. Its own audit obligation `hullDeterminantLogVolume` remains interface/pending.

## 8. Cross-cutting hidden assumptions

- `qSigned`/`Q_can`: never identified with the paper q-pilot; arbitrary Real in most layers; absolute-degree-normalized signed log is not asserted to be the q-pilot.
- `h`/`h_can`: arbitrary `targetSigned`/`thetaSigned`; finite hull volume model, not the IQ hull.
- `q_le_target`: assumed field; the hull-target constructor chooses target=hull volume, making the comparison tautological.
- `IPL/SHE/APT`: arbitrary `Prop` fields with evidence; not source theorems.
- `cor312Conclusion`: conditional on the contract/certificate fields; no construction of those fields.
- No actual `CompleteC`, BPS, Theta-pilot, or C1 object in the probe.

## 9. Accept/reject table

| file | verdict | exact reason |
|---|---|---|
| C9IUTBridgeProbe.lean | ACCEPT probe only / REJECT bridge | #check only; no theorem/composition |
| SourceTheorem311ReferenceContract.lean | ACCEPT contract / REJECT C1 | actual source-facing record, but conditional on SourceP1P2Bundle; no q/h/C1 |
| ContractSourceReduction.lean | REJECT source proof | arbitrary q/theta/target; q_le_hull assumed; hull target tautological; header admits q-pilot identification not asserted |
| ParametricStepXI.lean | REJECT C1 bridge | toy q/target/theta and comparison fields; conditional schema |
| SourceHullInterfaceDischarge.lean | ACCEPT model/obstruction / REJECT discharge | F1 normed model, F2 top obstruction; actual IQ carrier not realized |
| SourceQSideComparison.lean | ACCEPT local lemmas / REJECT paper bridge | arbitrary q; paper-faithful q carrier and comparison not constructed; hq slot degenerate |
| Volume.lean | ACCEPT algebra / REJECT source hull | explicit finite model; arbitrary hull/q/theta; not IUT hull |

## 10. Final integration verdict

**The IUT bridge is not accepted as an integration proof of Cor3.12/C1.** The probe only checks names. The actual source-facing contract is conditional; the consumer layers supply arbitrary q/h/target fields and assume the key comparisons; the hull interface discharge and q-pilot comparison remain open; the finite model is not the source hull. There is no `sorry`/`axiom` in the reviewed files, but the open source cards are encoded as explicit fields/inputs, which is exactly the gap, not a closure. No toy field is accepted as source data.

No Lean edits; no mixed/E3. target_accepted=false; kernel_closed=false.
