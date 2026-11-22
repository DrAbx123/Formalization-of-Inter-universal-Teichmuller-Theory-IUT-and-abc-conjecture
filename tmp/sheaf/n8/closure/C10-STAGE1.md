# C10 — N8 Assembly: SHEAF stage-1 record (revised)

任务 ID / 所属组 / owner / 日期：C10 / N8 closure / primespine / 2026-10-22
目标节点 / SHEAF 阶段：C10 N8Assembly / stage 1 (interface and dependency record), no Lean.
文件：write tmp/sheaf/n8/closure/C10-STAGE1.md (this file). No Lean file is written or changed in this package.
集成负责人 / 构建负责人：C10 integration owner; build not applicable in this package.
共享接口与冲突：C0 stage 1 freezes the input role l,V,I and the output roles. C10 must use those roles. No discarded C0 Lean trial is a statement dependency.
续领范围：after review, C0 stage 2 output type freeze; then C1 SourceInputBinding and C3 SourcePilotRegion as separate nodes.

## 0. Correction from the audit

This record supersedes the earlier C10-STAGE1 draft. The earlier draft wrongly
treated a discarded C0 stage-1 Lean trial as if its input/output records were
existing real types. C0-STAGE1.md states that C0 Lean is not finalized in stage 1
and that the earlier trial is a discarded candidate. Therefore:

- C10 does not import or depend on any discarded C0 Lean trial.
- N8TargetOutput is only a planned name, to be defined by C0 stage 2. It is not
  an existing Lean type and C10 does not assume it.
- The C4 generic schema SourceWitnessedOutput.lean is an unaccepted stage-2
  trial, not a statement dependency. It may be cited only with that label.
- Names such as SourceInputBindingData, SourceLogKummerData, SourcePilotRegionData,
  SourceAlgorithmCompatibilityData, PaperNormalizedVolumeData,
  SourceHolomorphicHullData, SourceDegreeComparisonData and
  SourcePilotApproximationData are placeholders "to define" in C1-C9 stage 2,
  not existing Lean types.

## 1. Mathematical target (from C0 stage 1)

C0 stage 1 fixes the N8 target roles, not an existing Lean type.

Allowed input (paper-given; not produced by the chain):

    l : PrimeGeFive
    V : Type uv
    I : OriginalInput.{u, uv, upi, umon, ui} l V

with I.initial : SourceDefinition31Data, I.family : SourceHodgeTheaterFamily,
I.index_equiv and I.arithmetic_alignment.

Output role O (to be frozen as an actual type only by C0 stage 2):

    (1) actual SourceTheorem311Realization data (procession, packet, vertical,
        evaluation, genericFamily, labelledCount) and Theorem 3.11 (a)(b)(c);
    (2) actual IPL/SHE/APT algorithm compatibility, not free ipl/she/apt Props;
    (3) actual source holomorphic hull and normalized log-volume, finite and
        positive;
    (4) actual q-pilot value Q(I), theta hull value Theta(I), finite Theta(I), and
        Q(I) <= Theta(I);
    (5) actual arithmetic degree / determinant / weight correspondence (Ob3-3).

The paper input also allows a place v, an actual source image realization,
a theta-pilot carrier n and a signed label j; C0 stage 1 assigns these to the
chain (C1/C3), not to the free C0 input. They must be produced/bound from the
same I, not passed as unrelated free data.

C0 stage 2 must define each output field separately with a real type/obligation,
source and consumer. It must not package the whole target as one opaque
Nonempty C0 output record, and it must not use StepXIContract's free
ipl/she/apt/qSigned fields.

## 2. C0-C9 exact responsibilities

### C0 Target signature
- C0 stage 1 (accepted scope): frozen allowed input l,V,I and output roles above.
- C0 stage 2 (to define): actual output type(s) for the five roles, each with its
  real donor type or an explicit named obligation. No total-goal sorry as the
  output definition.
- C0 is not a C10 input theorem. C10 must not consume a C0 existence proposition.

### C1 SourceInputBinding
- Input: same l, V, I : OriginalInput.
- Produce: actual binding of the arithmetic field/place, prime-strip,
  Frobenioid/theater and local/global source data to that same I; finite support
  and comparison statements; no projection of one I field renamed as a new
  binding.
- Data name: SourceInputBindingData (to define).
- Consumers: C2, C3, C6, C10.

### C2 SourceLogKummerRealization
- Input: I plus C1 binding.
- Produce: actual local log, kernel/image, Kummer arrow, action descent and
  K1/K2 source realization; precise Kummer/log-volume separation kept separate.
- Data name: SourceLogKummerData (to define).
- Consumers: C4, C5, C9, C10.

### C3 SourcePilotRegion
- Input: I plus C1 binding.
- Produce: actual q/theta-pilot in the completed local field, Kummer
  representation, tensor/region landing, root-change compatibility.
- Data name: SourcePilotRegionData (to define).
- Consumers: C4, C9, C10.

### C4 SourceWitnessedOutput
- Input: I, plus actual N, X, Y, C, eval and Ind1/Ind2/Ind3 data from C2/C3.
- Produce: the actual constrained choice family C(I,n,x), eval, possible-image
  U(I,n,x) = {y | exists c, eval c = y} with dependent-pair witnesses; Ind1/Ind2
  actual actions; separate Ind3 nonarchimedean inclusion and archimedean
  surjection, with source local-place indexing.
- Data name: SourceWitnessedOutputData (to define).
- Consumers: C5, C7, C10.
- The existing SourceWitnessedOutput.lean is an unaccepted generic stage-2
  trial. It may be consulted only as a schema; it is not a C10 statement dep and
  its generic C0Signature is not the actual source interface.

### C5 SourceAlgorithmCompatibility
- Input: C2, C3, C4 over the same I.
- Produce: actual IPL/SHE/APT algorithm compatibility, actual permission families
  and operation correspondence; Ind1/Ind2/Ind3 laws as source statements.
- Data name: SourceAlgorithmCompatibilityData (to define).
- Consumers: C7, C9, C10.

### C6 PaperNormalizedVolume
- Input: C1/C3/C4 actual local/global data and the paper-local D, O, weights.
- Produce: actual local/packet/global normalization, local/tuple weights,
  procession average and numerical reindexing; source instances of the
  normalization identities.
- Data name: PaperNormalizedVolumeData (to define).
- Consumers: C8, C10.

### C7 SourceHolomorphicHull
- Input: C4 U family, C5 compatibility, C6 weights, actual source data.
- Produce: common holomorphic hull containing the permitted image family,
  positive finite volume, and qPilot membership; no per-choice bound or free
  compactness input.
- Data name: SourceHolomorphicHullData (to define).
- Consumers: C10; C8 uses its real lattice/vector data.

### C8 SourceDegreeComparison
- Input: C6 normalized data and C7 real lattice/vector data.
- Produce: actual relative determinant, tensor power, global arithmetic
  degree/log-volume equality; Ob3-3 interface.
- Data name: SourceDegreeComparisonData (to define).
- Consumers: C9, C10.

### C9 SourcePilotApproximation
- Input: C2 log-Kummer, C3 actual q, C5 compatibility, C8 degree/log-volume.
- Produce: Values(I), actual allowed output values from the same construction;
  actual_values_bounded and actual_q_approximated; derive signed Q(I) <= Theta(I)
  without taking hq as an input. Values must not be defined as Set.Iic Theta.
- Data name: SourcePilotApproximationData (to define).
- Consumer: C10.

### C10 N8Assembly
- Input: l, V, I : OriginalInput and explicit C1-C9 data/proof parameters for
  the same l,V,I.
- Output: the actual C0 stage-2 output type.
- Natural proof: C1 gives the source binding; C2/C3 give the actual log-Kummer
  and pilot; C4 gives the witness family/Ind data; C5 gives IPL/SHE/APT
  compatibility; C6/C7 give normalized volume and the common hull; C8 gives
  determinant/arithmetic degree; C9 gives the actual q values and Q <= Theta.
  C10 then fills the C0 output fields: 3.11 realization from C1-C5, hull
  finite/positive and qPilot membership from C7, and Q <= Theta from C9 (with
  C7 bound and C8 readout).
- C10 may take C1-C9 as explicit function parameters. Each such parameter must
  be an actual data/proof structure, not a free proposition restating the goal.

## 3. What must actually be produced

- Actual source binding data for the arithmetic field/place/strip/Frobenioid/
  theater, from the given I.
- Actual local log/Kummer data with kernel/image/descent and K1/K2.
- Actual q/theta-pilot, Kummer class, tensor region and root compatibility.
- Actual N, X, Y, constrained C, eval, U and dependent-pair witnesses.
- Actual Ind1/Ind2 actions and separate Ind3 nonarchimedean inclusion /
  archimedean surjection with source indexing.
- Actual IPL/SHE/APT algorithm compatibility and permission-family coverage.
- Actual local/packet/global normalized volume and tuple/procession weights.
- Actual common holomorphic hull with positive finite volume and qPilot
  membership.
- Actual determinant/tensor-power/arithmetic-degree/Ob3-3 data.
- Actual Values(I), bound and approximation, and signed Q(I) <= Theta(I).
- Actual C0 stage-2 output fields, with the C0 stage-1 roles above.

## 4. Forbidden free conclusion inputs

C10 must not take as a parameter, structure field or C0 output field:

- ipl, she, apt : Prop;
- q_le_hull, q_le_target, target_le_theta, degree_preserved : Prop;
- hq (the final Q <= Theta inequality) or any renamed form;
- qSigned, thetaSigned, targetSigned as free numbers;
- arbitrary possibleImage : Set Y;
- StepXIContract or its ipl/she/apt/qSigned/thetaSigned fields;
- any discarded C0 trial output record or existence theorem;
- empty structures, True, PUnit, arbitrary Type, or Nonempty as substitutes for
  the actual objects above.

C1-C9 function parameters are allowed only as actual source data/proof
structures that C10 consumes. A parameter whose type is a proposition equivalent
to a C0 output field is a forbidden conclusion input.

## 5. C1-C9 gap table

| Node | Actual type file/status | Data name (to define) | Statement dep | Proof dep | Consumer |
|---|---|---|---|---|---|
| C1 | absent | SourceInputBindingData | same I binding statements | actual field/place/strip/theater comparison | C2, C3, C6, C10 |
| C2 | absent | SourceLogKummerData | local log/Kummer/K1-K2 statements | actual log/kernel/descent source realization | C4, C5, C9, C10 |
| C3 | absent | SourcePilotRegionData | actual q/theta-pilot/region statements | actual local element/tensor/root compatibility | C4, C9, C10 |
| C4 | only unaccepted trial SourceWitnessedOutput.lean | SourceWitnessedOutputData | actual C/eval/U/Ind type | actual N/X/Y/C/eval/actions and laws | C5, C7, C10 |
| C5 | absent | SourceAlgorithmCompatibilityData | IPL/SHE/APT compatibility type | actual algorithm/permission coverage | C7, C9, C10 |
| C6 | absent; partial Group6 donors | PaperNormalizedVolumeData | local/packet/global normalization type | source normalization instances | C8, C10 |
| C7 | absent; partial LocalFieldProductHull donors | SourceHolomorphicHullData | common hull/volume/qPilot membership type | actual common hull and positive finite volume | C8, C10 |
| C8 | absent | SourceDegreeComparisonData | determinant/degree/Ob3-3 type | actual determinant/tensor/global degree equality | C9, C10 |
| C9 | absent | SourcePilotApproximationData | Values/bound/approximation type | actual Values and Q <= Theta | C10 |
| C10 | this record; no Lean | C0 stage-2 output type | N8 output role type (C0 stage 2) | all C1-C9 data/proofs | Cor 3.12 / Cor312ToABCBridgeInterface |

All "data name" entries are to define in their own stage-2 packages. None is an
existing Lean type.

## 6. C10 dependency graph

    C0 stage 1: allowed input l,V,I and output roles
      -> C1 SourceInputBinding
      -> C2 SourceLogKummerRealization
      -> C3 SourcePilotRegion
      -> C4 SourceWitnessedOutput
      -> C5 SourceAlgorithmCompatibility
      -> C6 PaperNormalizedVolume
      -> C7 SourceHolomorphicHull
      -> C8 SourceDegreeComparison
      -> C9 SourcePilotApproximation
      -> C10 N8Assembly
      -> C0 stage 2: actual output type
      -> Cor 3.12 / Cor312ToABCBridgeInterface consumer

Auxiliary edges:
- C0 stage 1 -> C6 (input/local normalization roles)
- C2 -> C4/C5/C9
- C3 -> C4/C9
- C4 -> C5/C7
- C5 -> C7/C9
- C6 -> C8
- C7 -> C8/C10
- C8 -> C9
- C9 -> C10

## 7. First non-composable position

There is no composable C10 edge yet, for two concrete reasons:

1. C0 stage 2 output type is not defined.
   C0 stage 1 freezes only the output roles (3.11 realization, IPL/SHE/APT,
   hull/volume, q/theta values, arithmetic degree). It explicitly forbids
   packaging them into a single opaque Nonempty C0 output record before each
   field has a real type/obligation. No discarded C0 Lean trial supplies that
   type. Therefore C10 has no actual codomain type to construct at present.

2. C1-C9 actual types are not defined.
   SourceInputBindingData, SourceLogKummerData, SourcePilotRegionData,
   SourceWitnessedOutputData, SourceAlgorithmCompatibilityData,
   PaperNormalizedVolumeData, SourceHolomorphicHullData,
   SourceDegreeComparisonData and SourcePilotApproximationData are names to
   define, not existing Lean types. C4's SourceWitnessedOutput.lean is an
   unaccepted generic schema only. Therefore C10 cannot import or call any
   actual named C1-C9 interface yet.

First concrete type gap to resolve: C0 stage 2 must freeze one output field type
(or a record of separately justified field types) from the C0 stage-1 output
roles. In parallel but independently, C1 must define SourceInputBindingData from
the given OriginalInput. C10 cannot be written as Lean before at least the C0
stage-2 output type and C1's actual type exist.

The earlier empty-structure N8Assembly.lean is not a valid artifact and is not a
dependency of this record. It must not be promoted; it is left untouched.

## 8. Stage-1 acceptance statement

statement_compiles: not applicable (no Lean declaration in this stage).
proof_body_checked: not applicable.
kernel_closed: not applicable.
target_accepted: not applicable.

This record freezes the C10 target roles from C0 stage 1, the C0-C9
responsibilities, the must-be-produced objects, the forbidden free inputs, the
C1-C9 gap table, the dependency graph, and the first non-composable type
position. No Lean or production file is changed. Stop after this stage-1 record.
