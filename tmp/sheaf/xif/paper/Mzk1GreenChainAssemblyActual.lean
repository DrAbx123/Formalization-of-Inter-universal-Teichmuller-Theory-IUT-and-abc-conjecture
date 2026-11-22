/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S981TensorRegionHullFiniteActual
import tmp.sheaf.xif.paper.S945TensorPacketPaperSActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

/-! # A1125: green-chain assembly (S971/S979/S981) for our variant -/

/-
| field | value |
|---|---|
| Status | PARTIAL (containment inequality chain PROVED; identification to our A/R is explicit GAP) |
| green 链 | `LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual.qPilotPaperImageInLValued ⊆ tensorRegionHull`（S971:61）⇒ `qPilotTensorLog ≤ tensorRegionHullLog`（S979:59，条件 pos/fin） |
| 真证 | `RNorm_le_ANorm`; `M_nonneg`; `our_variant_of_identification` |
| GAP | GAP-NORM2：`A = ANorm`（q 侧 `A = paperQAbsLog l logQ` 与 `-qPilotTensorLog` 的识别；含 unitRegion 归一化） |
| GAP | GAP-RNORM：`R = RNorm`（`R = S2717ThetaHullLogVolume` 与 `-tensorRegionHullLog` 的识别；不同 carrier/measure） |
| GAP | GAP-CARRIER：`FinalLValuedCarrier T b`（native data T, per-b）与 C3 `C3LogShellTensorBlock C3` 不是同一载体 |
| 循环性 | no target assumed; identifications are explicit Props |
-/

noncomputable section
open scoped BigOperators TensorProduct
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S974TensorHullFiniteActual
open LeanFormal.IUT.XiFPaper.S971TensorRegionImageActual
open LeanFormal.IUT.XiFPaper.S979TensorRegionHullInequalityActual
open LeanFormal.IUT.XiFPaper.S981TensorRegionHullFiniteActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S962TensorPacketPaperInequalityActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1GreenChainAssemblyActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (D : FinalLTensorLogVolumeData T b)

/-- Our normalized q-side value: `A = -qPilotTensorLog`. -/
def ANorm : Real := - qPilotTensorLog T b D

/-- Our normalized theta-hull value: `R = -tensorRegionHullLog`. -/
def RNorm : Real := - tensorRegionHullLog T b D

/-- **Green chain (PROVED)**: `qPilotPaperImage ⊆ tensorRegionHull` gives `RNorm <= ANorm`. -/
theorem RNorm_le_ANorm
    (hpos : 0 < D.measure (LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual.qPilotPaperImageInLValued T b))
    (hfin : D.measure (tensorRegionHull T b D) < ⊤) :
    RNorm T b D ≤ ANorm T b D := by
  unfold RNorm ANorm
  have h := qPilotTensorLog_le_tensorRegionHullLog T b D hpos hfin
  linarith

/-- **Green chain (PROVED)**: `0 <= ANorm - RNorm`. -/
theorem M_nonneg
    (hpos : 0 < D.measure (LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual.qPilotPaperImageInLValued T b))
    (hfin : D.measure (tensorRegionHull T b D) < ⊤) :
    0 ≤ ANorm T b D - RNorm T b D := by
  have h := RNorm_le_ANorm T b D hpos hfin
  linarith

/-- Identification of the scalar `A` with `ANorm` (explicit GAP). -/
def AIdentification (A : Real) : Prop := A = ANorm T b D

/-- Identification of the scalar `R` with `RNorm` (explicit GAP). -/
def RIdentification (R : Real) : Prop := R = RNorm T b D

/-- **Assembly (PROVED, conditional on the two identifications)**: `0 <= A - R`. -/
theorem our_variant_of_identification {A R : Real}
    (hA : AIdentification T b D A)
    (hR : RIdentification T b D R)
    (hpos : 0 < D.measure (LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual.qPilotPaperImageInLValued T b))
    (hfin : D.measure (tensorRegionHull T b D) < ⊤) :
    0 ≤ A - R := by
  unfold AIdentification at hA
  unfold RIdentification at hR
  rw [hA, hR]
  exact M_nonneg T b D hpos hfin

def greenChainRows : List (String × String) :=
  [ ("qPilotPaperImage_subset_tensorRegionHull", "S971:61 containment (green)") ,
    ("qPilotTensorLog_le_tensorRegionHullLog", "S979:59 inequality (green, pos/fin)") ,
    ("ANorm / RNorm", "A := -qPilotTensorLog, R := -tensorRegionHullLog") ,
    ("RNorm_le_ANorm / M_nonneg", "PROVED from green chain") ,
    ("our_variant_of_identification", "0 <= A - R (PROVED, conditional on identifications)") ,
    ("GAP-NORM2", "A = paperQAbsLog vs -qPilotTensorLog (unitRegion normalization)") ,
    ("GAP-RNORM", "R = S2717ThetaHullLogVolume vs -tensorRegionHullLog") ,
    ("GAP-CARRIER", "FinalLValuedCarrier T b vs C3LogShellTensorBlock C3") ]

theorem greenChainRows_length : greenChainRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GreenChainAssemblyActual