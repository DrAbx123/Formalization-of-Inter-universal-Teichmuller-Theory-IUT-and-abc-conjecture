import tmp.sheaf.n8.closure.NativeTorsionClauseActual
import tmp.sheaf.n8.closure.NativeReductionRestActual
import tmp.sheaf.n8.closure.NativeContractFromBadFinite
import tmp.sheaf.n8.closure.EtaSourceDefinition31NativeAttempt

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Native Definition31 objects assembly attempt

Assembles the actual reduction clause from the actual native partition/source
objects and records the remaining exact clause gaps.  Full SourceDefinition31Data
is not claimed: torsion full clause, orbicurve, sections, cusp and the five
arithmetic compatibility proofs are not constructed by native data.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeContractFromBadFinite
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.NativeTorsionClauseActual
open LeanFormal.IUT.N8Closure.EtaSourceDefinition31NativeAttempt
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.N8Closure.EtaNativeDefinition31ObjectsAssembly

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual selected/bad carriers. -/
abbrev selectedPlaces : Type := NativeSelectedPlaces X
abbrev badPlaces : Type := NativeBadPlaces X

/-- Actual reduction assembly: needs the explicit bad-finiteness source card
and the exact remaining reduction/q fields. -/
noncomputable def nativeReductionClauseOf
    (C : NativeSourceWithBadFinite X)
    (R : NativeReductionRestRemaining X) :
    SourceReductionClause (NativeSelectedPlaces X) (NativeBadPlaces X) :=
  nativeReductionOfBadFinite X C (nativeReductionRestOfRemaining X R)

/-- Actual native stable/multiplicative reduction data from clauses A/B. -/
noncomputable def nativeReductionPartial : NativeReductionStableMultiplicative X :=
  nativeReductionStableMultiplicative X

/-- Actual torsion datum from native Clause C (not the full SourceTorsionClause). -/
noncomputable def nativeTorsionPartial :
    SourceTorsionDatum l X.S.arithmetic := nativeTorsionDatum X

/-- Exact remaining targets for the full Definition 3.1 contract.  Each field
is an exact target proposition, not a filled arbitrary record. -/
structure NativeDefinition31RemainingTargets (X : N8NativeInput l) where
  /-- Full torsion clause target. -/
  torsion : NativeTorsionTarget l
  /-- Orbicurve clause target. -/
  orbicurve : NativeOrbicurveTarget
  /-- Sections clause target. -/
  sections : NativeSectionsTarget
  /-- Cusp clause target. -/
  cusp : NativeCuspTarget
  /-- Five arithmetic compatibility props. -/
  compatibility : NativeArithmeticCompatibilityTarget

/-- Assembly target: actual bad-finiteness, reduction-remaining fields, and the
five remaining source-clause targets. -/
structure NativeDefinition31AssemblyInputs (X : N8NativeInput l) where
  badFinite : NativeSourceWithBadFinite X
  reductionRest : NativeReductionRestRemaining X
  remaining : NativeDefinition31RemainingTargets X

/-- Exact gap predicate: no actual assembly inputs are constructed by native
data.  In particular the split-multiplicative/q fields and the full
torsion/orbicurve/sections/cusp clauses are missing. -/
def NativeDefinition31AssemblyGap : Prop :=
  ¬ Nonempty (NativeDefinition31AssemblyInputs X)

end LeanFormal.IUT.N8Closure.EtaNativeDefinition31ObjectsAssembly

end