import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import tmp.sheaf.n8.closure.C1SourceHaarConsumerIntegration
import tmp.sheaf.n8.closure.NativeC1

/-!
# Native SourceDefinition31Data attempt

Actual partial result: NativeArithmeticRootSide X is the arithmetic root of
X.S with its equality witness.  This is the S-side arithmetic root needed by
SourceHaarNativeArithmeticBridge, but it is not a full SourceDefinition31Data.

Decisive blocker for the full S: SourceDefinition31Data requires, besides
arithmetic, selectedPlaces, badPlaces, reduction/partition, torsion, orbicurve,
sections, cusp, and five arithmetic-clause compatibility propositions with
proofs.  SourceNativeInitialThetaData supplies arithmetic, the six-tuple source
and clauses A-F, but not those contract clause records or compatibility proofs.
The production file SourceDefinition31NativeContractBridgeReduction proves that
a native-to-contract bridge is equivalent (under the A2 gate) to contract-root
supply; no such bridge is constructed.  Hence native data alone does not
produce the contract clause package.

No arbitrary S is chosen.  The target is recorded exactly, and
NativeContractMissingFields lists the exact missing field package.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeSourceDefinition31ActualAttempt

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C1SourceHaarConsumerIntegration

universe u

variable {l : PrimeGeFive}

/-- Actual S-side arithmetic root: the native root with equality witness.
This is not a full SourceDefinition31Data. -/
structure NativeArithmeticRootSide (X : N8NativeInput l) where
  arithmetic : InitialThetaArithmeticData l
  arithmetic_eq : arithmetic = X.S.arithmetic

/-- Actual native arithmetic root side. -/
def nativeArithmeticRootSide (X : N8NativeInput l) :
    NativeArithmeticRootSide X where
  arithmetic := X.S.arithmetic
  arithmetic_eq := rfl

theorem nativeArithmeticRootSide_nonempty (X : N8NativeInput l) :
    Nonempty (NativeArithmeticRootSide X) :=
  ⟨nativeArithmeticRootSide X⟩

/-- Exact full-S target: a contract S with the native arithmetic root. -/
abbrev NativeSourceDefinition31ActualTarget (X : N8NativeInput l) : Prop :=
  ∃ S : SourceDefinition31Data.{0} l, S.arithmetic = X.S.arithmetic

/-- Exact conditional bridge S-side: if the full-S target is supplied, the
Wave22 arithmetic bridge is available at that S. -/
theorem sourceHaarNativeArithmeticBridge_of_actualTarget
    (X : N8NativeInput l) (h : NativeSourceDefinition31ActualTarget X) :
    ∃ S : SourceDefinition31Data.{0} l,
      SourceHaarNativeArithmeticBridge S X := by
  rcases h with ⟨S, hS⟩
  exact ⟨S, congrArg (fun A : InitialThetaArithmeticData l => A.Fmod) hS⟩

/-- The exact contract fields not supplied by native data.  This is the
blocker package; it is not filled from arbitrary data. -/
structure NativeContractMissingFields (X : N8NativeInput l) where
  selectedPlaces : Type
  badPlaces : Type
  reduction : SourceReductionClause selectedPlaces badPlaces
  torsion : SourceTorsionClause l
  orbicurve : SourceOrbicurveClause
  sections : SourceSectionClause
  cusp : SourceCuspClause
  arithmetic_reduction_compatibility : Prop
  arithmetic_reduction_compatibility_proved :
    arithmetic_reduction_compatibility
  arithmetic_torsion_compatibility : Prop
  arithmetic_torsion_compatibility_proved : arithmetic_torsion_compatibility
  arithmetic_orbicurve_compatibility : Prop
  arithmetic_orbicurve_compatibility_proved :
    arithmetic_orbicurve_compatibility
  arithmetic_section_compatibility : Prop
  arithmetic_section_compatibility_proved : arithmetic_section_compatibility
  arithmetic_cusp_compatibility : Prop
  arithmetic_cusp_compatibility_proved : arithmetic_cusp_compatibility

/-- A full S yields the missing-fields package: the target is exactly a filled
version of this package plus the arithmetic root. -/
noncomputable def nativeContractMissingFieldsOfSource
    {X : N8NativeInput l} (S : SourceDefinition31Data.{0} l) :
    NativeContractMissingFields X where
  selectedPlaces := S.selectedPlaces
  badPlaces := S.badPlaces
  reduction := S.reduction
  torsion := S.torsion
  orbicurve := S.orbicurve
  sections := S.sections
  cusp := S.cusp
  arithmetic_reduction_compatibility :=
    S.arithmetic_reduction_compatibility
  arithmetic_reduction_compatibility_proved :=
    S.arithmetic_reduction_compatibility_proved
  arithmetic_torsion_compatibility := S.arithmetic_torsion_compatibility
  arithmetic_torsion_compatibility_proved :=
    S.arithmetic_torsion_compatibility_proved
  arithmetic_orbicurve_compatibility :=
    S.arithmetic_orbicurve_compatibility
  arithmetic_orbicurve_compatibility_proved :=
    S.arithmetic_orbicurve_compatibility_proved
  arithmetic_section_compatibility := S.arithmetic_section_compatibility
  arithmetic_section_compatibility_proved :=
    S.arithmetic_section_compatibility_proved
  arithmetic_cusp_compatibility := S.arithmetic_cusp_compatibility
  arithmetic_cusp_compatibility_proved :=
    S.arithmetic_cusp_compatibility_proved

theorem nativeSourceDefinition31ActualTarget_requires_missingFields
    (X : N8NativeInput l) (h : NativeSourceDefinition31ActualTarget X) :
    Nonempty (NativeContractMissingFields X) := by
  rcases h with ⟨S, _hS⟩
  exact ⟨nativeContractMissingFieldsOfSource S⟩

end LeanFormal.IUT.N8Closure.NativeSourceDefinition31ActualAttempt
