/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib
import Mathlib.Tactic
/-! # P0.6 gap①: continuous linear equivalence root extension -> p-adic coordinates -/
noncomputable section
set_option synthInstance.maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.Mzk1P0RootCoordEquivActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
abbrev rootCoordDim : Nat :=
  Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
noncomputable def rootCoordEquiv :
    rootNormedExtension T b ≃L[ℚ_[(qVFamTensorP T b)]]
      (Fin (rootCoordDim T b) → ℚ_[(qVFamTensorP T b)]) where
  toLinearEquiv := (Module.finBasis ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)).equivFun
  continuous_toFun :=
    LinearMap.continuous_of_finiteDimensional
      (Module.finBasis ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)).equivFun.toLinearMap
  continuous_invFun :=
    LinearMap.continuous_of_finiteDimensional
      (Module.finBasis ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)).equivFun.symm.toLinearMap
end LeanFormal.IUT.XiFPaper.Mzk1P0RootCoordEquivActual
end
