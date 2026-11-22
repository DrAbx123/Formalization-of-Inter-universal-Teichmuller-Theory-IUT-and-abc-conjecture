# S154: q-value object naming audit

Date: 2026-10-29.

## Per-object classification

| Lean object | Actual q sort | Evidence | Note |
|---|---|---|---|
| qVFamily T b : FinitePlaceQCandidate | q-parameter q_v (single underline) | QPilotZeroLocusDivisorActual: clause-B comparison parameter q | q-parameter value, not root |
| qVFamily T b .q | q-parameter element in completion | field of FinitePlaceQCandidate | q-parameter |
| sourceQUnit T b | unit attached to q-parameter q_v | PaperC3SourceDataQConsistencyActual: candidate unit of qVFamily q | q-parameter unit, NOT root |
| qVFamNormalizedGenerator T b | normalized q-parameter generator | QVFamNormalizedGeneratorSupplyActual: equals (qVFamily T b).q | q-parameter; name 'generator' refers to q_v, not 2l-root |
| thetaPacket.q | q-parameter q of the theta packet | FiniteThetaPacket ofQ q | q-parameter |
| thetaPacket.scale j | theta power q_v^(j^2) | realThetaValue q exponent | q-parameter power / theta value, NOT root |
| qVFamilyThetaPacket | packet from q-parameter norm | QVFamThetaImageActual | q-parameter packet |
| paperRootThetaUnit | 2l-th root theta unit | PaperC3ThetaRootActual | q-root |
| twoLthRootAt | actual 2l-th root of qUnit | PaperC3ThetaRootActual | q-root |
| candidateUnits place q | unit of q-parameter q | SourcePilotRegion | q-parameter unit; name is ambiguous |
| qUnit fields in ConcreteC3Donor* | q-parameter unit via candidateUnits | ConcreteC3DonorActual/Assembly | q-parameter unit; ambiguous name |

## Ambiguous qUnit names

The following identifiers are q-parameter units, not 2l-th roots:

* sourceQUnit
* concreteQUnit
* concreteC3QUnit
* qUnit fields in ConcreteC3DonorActual, ConcreteC3DonorAssemblyActual,
  ConcreteC3RootCompletionActual
* candidateUnits

Exact note: these are q-parameter (single-underline) units.  They must not be
read as q-root units.  The q-root objects are named paperRootThetaUnit and
twoLthRootAt.

A future mechanical rename to qParameterUnit would reduce ambiguity but would
touch many consumers; this audit records the exact semantics instead of a
non-essential global rename.

## Theta power vs root

thetaPacket.scale j = q^(j^2) is a power of the q-parameter, not the
2l-th root q_v.  The root-side theta values are paperRootThetaUnit and
paperRootThetaValue.  No equality between thetaPacket.scale and the root theta
unit is asserted.

## Conclusion

No object was found that mathematically identifies a q-parameter with a q-root.
The only issue is naming: several qUnit identifiers and
qVFamNormalizedGenerator mean q-parameter; exact notes are recorded.  No Lean
rename is required for correctness, and no fake root/parameter equality is
introduced.
