/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S956TensorPacketLogVolumeExactActual
import tmp.sheaf.xif.paper.S965FinalLCarrierTopologyActual
import tmp.sheaf.xif.paper.S996FiniteQuotientLinearizationActual
import tmp.sheaf.xif.paper.S1004QVFamFiniteLinearizationActual
import Mathlib.Tactic

/-! # A1126: actual FinalL-valued data — construction and exact obstruction

| field | value |
|---|---|---|
| Goal | replace the arbitrary `measure`/`unitRegion` of `FinalLTensorLogVolumeData` by actual data via a finite linearization `FinalLValuedCarrier ≃ (Fin d → Qp)`. |
| Status | **RETRACTED / MODEL-DEPENDENT**: `FinalL = RootExtension = AlgebraicClosure` is not a finite extension of Qp, so the full `FinalLValuedCarrier` has no finite linearization and no additive Haar. The conditional transported-Haar declarations were removed because they cannot be instantiated on the full carrier. |
| Source | `PaperFinalLValuedTensorCarrierActual:42-46` (`FinalL = RootExtension = AlgebraicClosure`, `FinalLValuedCarrier = qVFamTensorBlock ⊗ FinalL`); `S996FiniteQuotientLinearizationActual:47-58` (`S996FinalLValuedFiniteModuleRequired`); `S1004QVFamFiniteLinearizationActual:6-10` (full carrier not finite-dimensional); `S956:31-41` (`FinalLTensorLogVolumeData` fields). |
| GAP | `Module.Finite/Free Qp (FinalLValuedCarrier)` is unprovable as stated; a finite quotient/finite root extension would be needed, changing the carrier. This file records the obstruction only; no Haar construction is asserted. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ActualFinalLDataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S996FiniteQuotientLinearizationActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- `FinalL` is the algebraic closure of the common completion, not a finite
extension. -/
theorem finalL_eq_algebraicClosure :
    FinalL T b = AlgebraicClosure (CommonPrimeCompletion ((finalLGeometry T b).place PUnit.unit)) := rfl

/-- The exact finite-module input needed for the finite linearization of the
full carrier (same as S996's exact obstruction). -/
def FinalLCarrierFiniteDimensionalRequired : Prop :=
  Module.Finite ℚ_[(qVFamTensorP T b)] (FinalLValuedCarrier T b) ∧
    Module.Free ℚ_[(qVFamTensorP T b)] (FinalLValuedCarrier T b)

theorem finalLCarrierFiniteDimensionalRequired_iff :
    FinalLCarrierFiniteDimensionalRequired (l := l) T b ↔
      (Module.Finite ℚ_[(qVFamTensorP T b)] (FinalLValuedCarrier T b) ∧
        Module.Free ℚ_[(qVFamTensorP T b)] (FinalLValuedCarrier T b)) := Iff.rfl

-- RETRACTED: the conditional transported-Haar construction was removed because
-- `FinalLValuedCarrier` has no `MeasurableSpace`/finite linearization on the full
-- algebraic-closure carrier.  Do not reintroduce it as a green object.

/-- Exact construction GAP: no finite linearization of the full FinalL-valued
carrier exists as stated, because `FinalL` is an algebraic closure; no
transported Haar on the full carrier is available. -/
def ActualFinalLDataConstructionGap : Prop :=
  FinalLCarrierFiniteDimensionalRequired (l := l) T b

-- no transported-Haar theorem: retracted with the construction above.

def rows : List (String × String × String) :=
  [ ("finalL_eq_algebraicClosure", "FinalL = AlgebraicClosure", "rfl"),
    ("FinalLCarrierFiniteDimensionalRequired", "Finite+Free Qp carrier", "GAP (unprovable)"),
    ("ActualFinalLDataConstructionGap", "no finite linearization on full carrier", "GAP") ]

theorem rows_length : rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ActualFinalLDataActual

end