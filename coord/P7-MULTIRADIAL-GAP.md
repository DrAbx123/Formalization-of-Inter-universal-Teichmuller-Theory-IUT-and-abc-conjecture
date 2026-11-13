# GAP-P7-MULTIRADIAL — xi-e/xi-f multiradial production search

Status: **PARTIAL** — finite model production green; general conditional bridge green;
actual xi-e/xi-f production missing. Date: 2026-11-13. Owner: stepxi.

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