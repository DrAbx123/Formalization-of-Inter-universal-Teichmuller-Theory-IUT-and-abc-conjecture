# GAP-P7-MULTIRADIAL — xi-e/xi-f multiradial production search

Status: **PARTIAL/OPEN** — finite model production green; general conditional bridge green; C3 actual Kummer/Theta source candidate extracted (2026-11-13); actual xi-e/xi-f production `n,oR_LGP` still missing. Date: 2026-11-13. Owner: stepxi.

## Search result

Reusable declarations exist, but only as a finite/kernel model, not as the
actual IUT II/III xi-e/xi-f multiradial production.

1. `LeanFormal/IUT/IUTIII/Theorem311/MultiradialOutputKernel.lean`
   - `MultiradialKernel.Core` (base/level, ind1/ind2/ind3, kernel laws) and
     `Profile` (logVolume, possibleImage, invariant laws).
   - This is an abstract kernel interface; no Hodge theater/F-prime-strip.
2. `LeanFormal/IUT/IUTIII/Theorem311/SourceFiniteMultiradial.lean`
   - finite Q(i)-at-5 model: `core l`, `profile l`, log-volume formula.
   - its header explicitly says it is a finite model boundary, not the source
     theorem about arbitrary Hodge theaters.
3. `LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithmReduction.lean`
   - kernel-level route construction and Ind1/Ind2/Ind3 commutation;
     conditional on the source prerequisite package; header explicitly says
     finite Q(i)-at-5 carrier only and does not construct the actual package.
4. `vendor/promachina/snapshots/.../Iut/Stage1/IUTStage1Theorem311.lean`
   - fields `step_xi_e_log_volume_set_linked_to_fixed_q_volume` and
     `step_xi_f_q_volume_lies_in_theta_upper_ray` at approx. lines 22223-22228
     are `Prop` fields, not constructions (no actual term/algorithm).
5. `Iut/Wall/Constraints.lean` / `Iut/Wall/README.md`
   - `EtaAlg.SHEq` / wall semantics for Step (xi-e/xi-f); these encode the
     north-wall condition, not a multiradial production.

## Finite production theorems (model only)

`LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithmReduction.lean`
contains concrete finite production theorems:
- `finiteIndeterminacyDischarge l`: Ind1/Ind2/Ind3 quotient laws for the
  single finite Q(i)-at-5 carrier;
- `finiteMultiradialAlgorithmDischarge l`: algorithm contract + route normal
  form + finite Ind1/2/3 quotient laws.

These are genuine proved theorems for the finite model, not the paper's actual
source production.  `Mzk1P7MultiradialCarrierActual.lean` re-exports them as
`finiteMultiradialAlgorithmDischarge_model` / `finiteIndeterminacyDischarge_model`
with axioms [propext, Classical.choice, Quot.sound], and is green
(DONE 2026-11-13T11:13:12Z).

## Carrier package (model only)

`tmp/sheaf/xif/paper/Mzk1P7MultiradialCarrierActual.lean` re-exports the
finite carrier `SourceFiniteMultiradial.core/profile` and one log-volume
theorem, with a header marking the port source and the model-only semantics.
It is NOT actual production and must not be cited as GAP discharge.

## Exact missing production types

Input side (partially present):
- actual `Theorem311Source.OriginalInput l V` exists (InitialThetaData +
  HodgeTheater family + index/arithmetic alignment);
- missing: actual D-prime-strip processions, vertical log-Kummer maps, and
  etale-theta data as input types.  No such structures are present.

Output side (absent):
there is NO Lean type for the paper's multiradial representation `n,oR_LGP`.
Precisely missing:
- a type of processions of D-prime-strips (functorial under isomorphism);
- a log-Kummer class / log-link transport output type;
- Theta-times-mu LGP-link compatibility data;
- IPL/SHE/APT output structures used by Remark 3.11.1(iii)-(iv);
- a production function
  `multiradial : OriginalInput l V -> MultiradialOutput l V`
  with Ind1/Ind2/Ind3 compatibility laws.
Only the abstract kernel `Core`/`Profile` has these laws; it is not the
paper output carrier.

## Assumption bridge: general vs finite

`finiteMultiradialAlgorithmDischarge l` assumptions:
- `l : PrimeGeFive`;
- concrete finite Q(i)-at-5 carrier `SourceFiniteParameterized.carrier l`;
- finite label group `Fl l = ZMod l` (commutative).

General level (`ParametricTheorem311.Carrier Label Choice`):
- `CarrierAlgorithmContract carrier` is UNCONDITIONAL (`carrierAlgorithmContract`);
- `RouteNormalForm carrier` is an explicit missing general input (finite proof
  only);
- `FiniteIndeterminacyDischarge l` is finite-label-specific; no general-label
  type/definition exists in the tree.

Conditional bridge file:
`tmp/sheaf/xif/paper/Mzk1P7MultiradialGeneralBridgeActual.lean`
- `GeneralMultiradialWitness` = carrier + `routeNormalForm`;
- `general_contract_and_routeNormalForm` bundles the unconditional contract
  and named route normal form.  No actual production is claimed.

## Finite witness in the general interface

`tmp/sheaf/xif/paper/Mzk1P7MultiradialWitnessActual.lean` (GREEN, DONE 2026-11-13T11:31:16.140Z, 45s; axioms [propext, Classical.choice, Quot.sound])
instantiates `GeneralMultiradialWitness` with the actual finite Q(i)-at-5
data (`SourceFiniteParameterized.Label/Choice/carrier`, `routeNormalForm_finite`).
This is a genuine finite witness for the general interface (contract +
route normal form), not a general production.

`FiniteIndeterminacyDischarge` cannot be generalized as-is: its fields are
definitionally tied to `ConcreteFiniteTheorem311.ProcessionChoice` and its
`upperSemiLevel`, and the abstract `Core` has no level-separation/injectivity
axioms.  No general witness is derivable from the frozen kernel interface.

## Conclusion

GAP-P7-MULTIRADIAL remains OPEN.  The only legitimate deliverable is the
model carrier package above plus this exact input/output gap.  No toy output
type or fake production function is introduced.

End of gap note.
## Update 2026-11-13: C3 actual source candidate

New file: tmp/sheaf/xif/paper/Mzk1P7MultiradialProductionActual.lean
(DONE 2026-11-13T13:19:40.689Z, 54s; olean 83552 B; axioms trio).

Constructed from the actual C3 data (`SourcePilotRegionData`):
- `C3MultiradialKummerSource` = the actual `SourcePilotRegionData` itself;
- `c3MultiradialKummerSource C3 : C3MultiradialKummerSource C3 := C3`;
- `c3Source_kummerClass`, `c3Source_rootChange`, `c3Source_tensorUnit` are
  actual projection theorems (rfl).

This is a genuine source-side candidate containing the actual Kummer class,
root-change tower, Theta packet, tensor unit/landing.  It is still NOT the
paper production `n,oR_LGP`: the output types and laws are recorded in
`MultiradialProductionMissing` (no inhabitant):
n, oR_LGP, dPrimeProcessions, logKummerClass transport, thetaMuLGP,
iplSheApt, Ind1/2/3 laws.

What can be constructed from C3 (actual):
- kummerClass, rootChange (and rootChange_eq), thetaPacket, qUnit,
  tensorUnit, tensorLanding, tensorLanding_q;
these are now available as actual C3 fields.

What cannot be constructed from C3:
- `n`/`oR_LGP` themselves, D-prime-strip processions, log-Kummer transport
  output, Theta×mu LGP compatibility, IPL/SHE/APT structures, and Ind laws;
no types/data for these exist in the tree.

Finite-model bridge: the finite witness uses `SourceFiniteParameterized`
Q(i)-at-5 (`l`-specific), while C3 uses actual `Fmod`/place/p; there is no
map between them, so the finite witness cannot be instantiated as C3
production.

Status remains PARTIAL/OPEN for actual production; no toy carrier is used.

End of 2026-11-13 update.
## Update 2026-11-14 14:10: A5 复核（Lead 查重）
- **已存在非平凡 production（green）**：`tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean`（olean True）——
  - `SourceMultiradialCarrier I := (sourceStepXICore I).GeneratedQuotient`（actual source core 的 Ind1/Ind2 商）；
  - `sourceMultiradialMap`、`sourceMultiradialLogVolume`（descend）、`sourceMultiradialPossibleImage`、`sourceMultiradialLevel`；
  - `sourceMultiradialMap_ind1`、`sourceMultiradialMap_ind2`（Ind1/Ind2 不变性）；
  - `sourceMultiradialPossibleImage_ind3_upper`（Ind3 upper-semi）、`sourceMultiradialLogVolume_ind3_le`、`sourceMultiradialLevel_ind3`；
  - `sourceMultiradialCarrier_nonempty`。
- 另有 green：`MultiradialProcessionActual`（PrcMember/PrcTransition/PrcAutomorphism/Ind1TensorAction/thetaLabelOfFin/sourceThetaValue/sourceLGPMonoid/sourceLGPAction 等 14 defs）、`Indet02BPSMultiradialUpToActual`、`Indet05RouteMultiradialClassActual`、`S3139SourceMultiradialConsumerActual`、`S3139MultiradialProcessionConsumerActual`。
- **因此旧结论“actual production 缺失”过时**：quotient-carrier 级 production 已有；真正剩余是 `SourceMultiradialMutationDemand`（first-triangle BPS → 该 quotient target，`S3139StageOneSeamsActual` 的 exact missing）以及完整 `n,oR_LGP` 输出类型/IPL-SHE-APT 兼容。

## Update 2026-11-14 14:25: A5 进一步查重（mutation demand 已有 inhabitant）
- `S3139FirstTriangleResidualActual.lean`（olean True）已有 **`sourceMultiradialMutationDemandInhabitant : SourceMultiradialMutationDemand J (sourceBPSOfTheater J 0 0) (sourceEtHTZeroColumn J 0)`**（`bps_glued := refl`, `etHT_zero_column := rfl`, `mutation := id`），以及 `sourceEtHTTarget_eq_bpsEtaleLikePortion`、`ind1_ind2_tprod_commute`。
- 该文件明确：A5 只差 **三个 residual `Nonempty` 数据**：`SourceProcessionCapsuleContract`、`SourceLGPData`、`SourceFmodRealEmbedding`，加 Ind1 与 actual procession action 识别、Ind3 log-Kummer 兼容；旧结论“n,oR_LGP production 缺失”过时。

## A5/#4 consumer entry (2026-11-14)

Actual A5 capsule/log-shell index, fixed-place Ind1 transport, and Ind3 tensor log-region inclusion are GREEN. See [P7-MULTIRADIAL-CONSUMER-FINAL.md](P7-MULTIRADIAL-CONSUMER-FINAL.md). General-place Ind1 remains the exact gap Ind1ShellTransportGap; do not fill with a toy/refl equivalence.
