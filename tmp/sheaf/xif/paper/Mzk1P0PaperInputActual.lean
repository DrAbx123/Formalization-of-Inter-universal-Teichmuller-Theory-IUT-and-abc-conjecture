/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0SourceDataBridgeActual
import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0ThetaAlignmentActual
import Mathlib.Tactic
/-! # P0.5: paper input package for the native/L comparison bridge -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P0SourceDataBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0ThetaAlignmentActual
open Definition31D4D9Supply
variable {l : PrimeGeFive}
/-- Paper Definition 3.1 input package: completion + D4D9 supply + native lattice/input +
index/place binding. Every field is paper-given data, not a new mathematical assumption. -/
structure P05PaperInput (l : PrimeGeFive) where
  C : SourceCompletion.{0} l
  S : D4D9Supply C.arithmetic
  X : N8NativeInput l
  hX : X.S = nativeThetaData C
  index_equiv : X.family.index ≃ SourceTheorem311Index
  binding : NativePlaceBindingDonors X
    (nativeOriginalInputOfDonors X (donorsOf C S X hX index_equiv))
variable (P : P05PaperInput l)
def paperDonors : NativeOriginalInputDonors P.X :=
  donorsOf P.C P.S P.X P.hX P.index_equiv
def paperOriginalInput : OriginalInput.{0, 0, 0, 0, 0} l (NativePlaces P.X.S) :=
  nativeOriginalInputOfDonors P.X (paperDonors P)
theorem paperOriginalInput_nonempty :
    Nonempty (OriginalInput.{0, 0, 0, 0, 0} l (NativePlaces P.X.S)) :=
  ⟨paperOriginalInput P⟩
def paperBinding :
    NativePlaceBindingDonors P.X (paperOriginalInput P) :=
  P.binding
theorem paper_sourceData_arithmetic :
    (P.S.toSourceData).arithmetic = P.C.arithmetic := rfl
theorem paperOriginalInput_initial :
    (paperOriginalInput P).initial = P.S.toSourceData := rfl
/-- Explicit comparison-bridge input: an L-side original input plus the two exact
readout equalities. This records the remaining mathematical bridge, not a new axiom. -/
structure PaperComparisonInput (l : PrimeGeFive) (P : P05PaperInput l) where
  I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  b : Bad (nativePlaceSelection (P.X.S))
  q_read_eq : qReadActual I place = nativeQReadout P.X.S b
  theta_read_eq : thetaReadActual I place = nativeThetaReadout P.X.S b
attribute [instance] PaperComparisonInput.hp
theorem LPaperInstance_of_paperComparison
    (B : PaperComparisonInput l P)
    (h : NativeComparison P.X.S B.b) :
    LPaperInstance B.I B.place := by
  unfold LPaperInstance
  change qReadActual B.I B.place ≤ thetaReadActual B.I B.place
  rw [B.q_read_eq, B.theta_read_eq]
  exact h
def rows : List String :=
  ["P05PaperInput: SourceCompletion + D4D9Supply + N8NativeInput + hX + index_equiv + binding",
   "paperDonors/paperOriginalInput construct NativeOriginalInputDonors/OriginalInput",
   "PaperComparisonInput records q/theta readout equalities (exact missing bridge)",
   "LPaperInstance_of_paperComparison: bridge + NativeComparison => LPaperInstance"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputActual
end