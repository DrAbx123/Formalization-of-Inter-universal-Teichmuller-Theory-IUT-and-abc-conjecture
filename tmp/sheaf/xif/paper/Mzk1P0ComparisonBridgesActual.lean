/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0PaperInputActual
import tmp.sheaf.xif.paper.Mzk1P0ThetaAlignmentActual
import tmp.sheaf.xif.paper.ConcreteC3DonorActual
import Mathlib.Tactic
/-! # P0.6: exact bridges for q/theta readouts and V-index -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0ComparisonBridgesActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0ThetaAlignmentActual
variable {l : PrimeGeFive}
variable (P : P05PaperInput l)
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (b : Bad (nativePlaceSelection P.X.S))
/-- Exact q bridge: L q readout equals native q readout. -/
def QReadoutBridge : Prop := qReadActual I place = nativeQReadout P.X.S b
/-- Exact theta bridge: L theta readout equals native theta readout. -/
def ThetaReadoutBridge : Prop := thetaReadActual I place = nativeThetaReadout P.X.S b
/-- V-index bridge: native place subtype can be identified with the paper prime strip 2..7. -/
def VIndexBridge : Prop := Nonempty (NativePlaces P.X.S ≃ FinitePrimePlace 2 7)
/-- Conditional paper comparison input from the three exact bridges. -/
def toPaperComparison (hq : QReadoutBridge P I place b)
    (hθ : ThetaReadoutBridge P I place b) : PaperComparisonInput l P where
  I := I
  p := p
  place := place
  b := b
  q_read_eq := hq
  theta_read_eq := hθ
theorem LPaperInstance_of_bridges
    (hq : QReadoutBridge P I place b)
    (hθ : ThetaReadoutBridge P I place b)
    (h : NativeComparison P.X.S b) : LPaperInstance I place :=
  LPaperInstance_of_paperComparison P (toPaperComparison P I place b hq hθ) h
def rows : List String :=
  ["QReadoutBridge: exact scalar equality; deeper missing canonical q-choice identification",
   "ThetaReadoutBridge: exact scalar equality; factor=exp(delta) proven, Haar normalization missing",
   "VIndexBridge: NativePlaces X.S vs FinitePrimePlace 2 7; no tree equivalence",
   "toPaperComparison + LPaperInstance_of_bridges: bridges + NativeComparison => LPaperInstance"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0ComparisonBridgesActual
end