# S491: aligned StageDivisor.{u} -> {u+1} divisor map

Date: 2026-10-29. Additivity only; naturality not proved.

## Stage divisor universe alignment

stageDivisorULiftEquiv':
  StageDivisor.{u} ≃+ StageDivisor.{u+1}
  via stageDivisorEquivNat and its inverse.

grothendieckStageDivisorULift':
  GrothendieckAddGroup StageDivisor.{u} ->+
  GrothendieckAddGroup StageDivisor.{u+1}.

## Lifted divisor map

liftedDivisorMapAligned' V :=
  grothendieckStageDivisorULift'.comp (liftedDivisorMap V).

liftedDivisorMapAligned'_add: additivity.

## Example32 divisor field

example32DivisorAlignedS491 V X:
  (example32RationalFunctionsLiftedULift).obj X ->+
  GrothendieckAddGroup ((example32PhiIsFSM K).obj X).carrier

via L := X.objDown.unop, Field L.obj.obj := L.property.toField,
Algebra K L.obj.obj := inferInstance, and liftedDivisorMapAligned' L (V X).

example32DivisorAlignedS491_add: additivity.

## S480 Input

Example32DivisorOnlyData packages valuationFamily, divisor, divisor_eq,
divisor_add (no naturality).

example32InputDataS491 fills S480 Example32InputData.divisor with the aligned
map, given explicit compatibility and an explicit naturality hypothesis.
Naturality is not proved here.

No fake divisor/naturality; no completion/L.
