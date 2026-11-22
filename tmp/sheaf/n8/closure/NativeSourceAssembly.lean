import tmp.sheaf.n8.closure.NativeSourceReductionActual
import tmp.sheaf.n8.closure.NativeSourceTorsionActual
import tmp.sheaf.n8.closure.NativeSourceOrbicurveActual
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import tmp.sheaf.n8.closure.C1BridgeProof
import tmp.sheaf.n8.closure.NativeBindingRFActual
import tmp.sheaf.n8.closure.NativeIndexActualAttempt
import tmp.sheaf.n8.closure.P6Bridge
import tmp.sheaf.n8.closure.NativeBadLiftActual
import tmp.sheaf.n8.closure.NativeOrbicurveFieldsActual
import tmp.sheaf.n8.closure.NativeReductionFieldsActual
import tmp.sheaf.n8.closure.C1ActualDataNative

/-! # Assemble the actual native SourceDefinition31Data

This file consumes the native SourceNativeInitialThetaData together with the exact source fields isolated by the clause constructors, and assembles the Definition 3.1 SourceDefinition31Data. The clause constructors are reused; no field is fabricated.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.NativeSourceTorsion
open LeanFormal.IUT.InitialThetaSource.NativeSourceOrbicurveActual
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.InitialThetaSource.NativeOrbicurveFieldsActual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C1BridgeProof

variable {l : PrimeGeFive}

/-- Exact source fields needed to assemble the Definition 3.1 contract from a native initial Theta datum. -/
structure NativeSourceAssembly (T : SourceNativeInitialThetaData.{0} l) where
  badFinite : NativeBadSetFinite T
  split : NativeSplitMultiplicativeAtLift T
  torsionGaps : NativeSourceTorsionGaps (A := T.arithmetic) (S := T.tuple.source) (C := T.clauseA) (B := T.clauseB) T.clauseC
  exactSequence : SourceExactSequenceClause
  curve : Type
  puncturedCurve : Type
  cover : Type
  structureGroup : Type
  [structureGroupLaw : Group structureGroup]
  curveToPunctured : puncturedCurve → curve
  coverToPunctured : cover → puncturedCurve
  cover_surjective : Function.Surjective coverToPunctured
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount
  d7 : NativeD7Intake (SourceCompletion.ofSourceNative T)
  cuspHyp : NativeCuspClauseHypotheses
  redCompat : Prop
  redCompat_proved : redCompat
  torCompat : Prop
  torCompat_proved : torCompat
  orbCompat : Prop
  orbCompat_proved : orbCompat
  secCompat : Prop
  secCompat_proved : secCompat
  cusCompat : Prop
  cusCompat_proved : cusCompat

namespace NativeSourceAssembly

variable {T : SourceNativeInitialThetaData.{0} l} (S : NativeSourceAssembly T)

noncomputable def toSourceData : SourceDefinition31Data.{0} l where
  arithmetic := T.arithmetic
  selectedPlaces := Selected (nativePlaceSelection T)
  badPlaces := Bad (nativePlaceSelection T)
  reduction := by
    letI : Fintype (Bad (nativePlaceSelection T)) :=
      Classical.choice (nativeBadSetFintype T S.badFinite)
    exact nativeReductionClauseOfPrimitives T S.split
  torsion := S.torsionGaps.toSourceTorsionClause
  orbicurve := by
    letI : Group S.structureGroup := S.structureGroupLaw
    exact nativeSourceOrbicurveClause S.exactSequence S.curve S.puncturedCurve S.cover
      S.structureGroup S.curveToPunctured S.coverToPunctured S.cover_surjective
      S.cuspCount S.cuspCount_pos
      (Nonempty (SourceOrbicurveFiniteEtaleCover T.tuple.source.xK T.tuple.source.cK))
      (curveCompatibility_of_clauseD T.clauseD)
  sections := nativeSectionClause (SourceCompletion.ofSourceNative T) S.d7
  cusp := nativeCuspClauseOfHypotheses S.cuspHyp
  arithmetic_reduction_compatibility := S.redCompat
  arithmetic_reduction_compatibility_proved := S.redCompat_proved
  arithmetic_torsion_compatibility := S.torCompat
  arithmetic_torsion_compatibility_proved := S.torCompat_proved
  arithmetic_orbicurve_compatibility := S.orbCompat
  arithmetic_orbicurve_compatibility_proved := S.orbCompat_proved
  arithmetic_section_compatibility := S.secCompat
  arithmetic_section_compatibility_proved := S.secCompat_proved
  arithmetic_cusp_compatibility := S.cusCompat
  arithmetic_cusp_compatibility_proved := S.cusCompat_proved

theorem toSourceData_arithmetic :
    S.toSourceData.arithmetic = T.arithmetic := rfl

end NativeSourceAssembly

/-- The native root plus the exact source fields yields NativeContractDatumExists. -/
theorem nativeContractDatumExists_of_assembly (X : N8NativeInput l)
    (S : NativeSourceAssembly X.S) : NativeContractDatumExists X :=
  ⟨S.toSourceData, rfl⟩

/-- The native donors built from the assembled contract and an explicit index equivalence. -/
noncomputable def assemblyDonors (X : N8NativeInput l)
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index) :
    NativeOriginalInputDonors X where
  initial := S.toSourceData
  initial_arithmetic := rfl
  index_equiv := e

noncomputable def assemblyInput (X : N8NativeInput l)
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index) :
    OriginalInput l (NativePlaces X.S) :=
  nativeOriginalInputOfDonors X (assemblyDonors X S e)

/-- The canonical P6 donor package from the assembled contract and the exact R/F source fields. -/
noncomputable def p6BridgeDonorsOfAssembly (X : N8NativeInput l)
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index)
    (R : LeanFormal.IUT.N8Closure.NativeBindingRFActual.NativeImageRealizationSourceFields
      X (assemblyInput X S e))
    (F : LeanFormal.IUT.N8Closure.NativeBindingRFActual.NativeFiberSourceFields
      X (assemblyInput X S e) (nativePlaceIndexEquiv X)) :
    P6BridgeDonors X where
  inputDonors := assemblyDonors X S e
  bindingDonors := LeanFormal.IUT.N8Closure.NativeBindingRFActual.nativePlaceBindingDonorsOfSource
    X (assemblyInput X S e) (nativePlaceIndexEquiv X) R F

theorem c1ActualData_nonempty_of_assembly (X : N8NativeInput l)
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index)
    (R : LeanFormal.IUT.N8Closure.NativeBindingRFActual.NativeImageRealizationSourceFields
      X (assemblyInput X S e))
    (F : LeanFormal.IUT.N8Closure.NativeBindingRFActual.NativeFiberSourceFields
      X (assemblyInput X S e) (nativePlaceIndexEquiv X)) :
    Nonempty (C1ActualData (assemblyInput X S e)) :=
  ⟨c1ActualDataOfNativeDonors X (assemblyDonors X S e)
    (p6BridgeDonorsOfAssembly X S e R F).bindingDonors⟩

theorem sourceInputBinding_nonempty_of_assembly (X : N8NativeInput l)
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index)
    (R : LeanFormal.IUT.N8Closure.NativeBindingRFActual.NativeImageRealizationSourceFields
      X (assemblyInput X S e))
    (F : LeanFormal.IUT.N8Closure.NativeBindingRFActual.NativeFiberSourceFields
      X (assemblyInput X S e) (nativePlaceIndexEquiv X)) :
    Nonempty (SourceInputBinding (assemblyInput X S e)) :=
  ⟨sourceInputBindingOfNativeDonors X (assemblyDonors X S e)
    (p6BridgeDonorsOfAssembly X S e R F).bindingDonors⟩

end LeanFormal.IUT.N8Closure.C1Actual
end