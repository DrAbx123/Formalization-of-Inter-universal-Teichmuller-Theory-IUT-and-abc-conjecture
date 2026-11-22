/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply
import tmp.sheaf.n8.closure.C10BridgeProof
import tmp.sheaf.n8.closure.NativeInput
import Mathlib.Tactic
/-! # P0.5: SourceDefinition31Data assembly from SourceCompletion + D4D9 supply -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0SourceDataBridgeActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open Definition31D4D9Supply
variable {l : PrimeGeFive}
def nativeThetaData (C : SourceCompletion.{0} l) : SourceNativeInitialThetaData.{0} l :=
  C.toSourceNativeInitialThetaData
theorem nativeThetaData_arithmetic (C : SourceCompletion.{0} l) :
    (nativeThetaData C).arithmetic = C.arithmetic := rfl
/-- Conditional donor constructor: completion C, D4D9 supply, native input over T_C and index equivalence. -/
def donorsOf (C : SourceCompletion.{0} l) (S : D4D9Supply C.arithmetic)
    (X : N8NativeInput l) (hX : X.S = nativeThetaData C)
    (e : X.family.index ≃ SourceTheorem311Index) : NativeOriginalInputDonors X where
  initial := S.toSourceData
  initial_arithmetic := by
    rw [hX, nativeThetaData_arithmetic]
    rfl
  index_equiv := e
/-- From donors, the contract OriginalInput exists (all universes pinned to 0). -/
theorem originalInput_of_donors (X : N8NativeInput l) (D : NativeOriginalInputDonors X) :
    Nonempty (OriginalInput.{0, 0, 0, 0, 0} l (NativePlaces X.S)) :=
  ⟨nativeOriginalInputOfDonors X D⟩
def QBridgeMissingInputs (C : SourceCompletion.{0} l) : Prop :=
  Nonempty (NativeLattice (nativeThetaData C)) ∧
    ∃ (X : N8NativeInput l), X.S = nativeThetaData C ∧
      Nonempty (X.family.index ≃ SourceTheorem311Index)
def rows : List String :=
  ["SourceCompletion.toSourceNativeInitialThetaData supplies T arithmetic/tuple/clauses A-F",
   "D4D9Supply.toSourceData supplies SourceDefinition31Data and arithmetic = C.arithmetic",
   "donorsOf: completion + D4D9 + native input + index equivalence -> NativeOriginalInputDonors",
   "missing: D4D9Supply (D4/D5/D9 cards), NativeLattice T, index equivalence, place binding, q equality"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0SourceDataBridgeActual
end