/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A1LatticeCompareActual
import tmp.sheaf.xif.paper.Mzk1SaturationBasesDataActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.Tactic

/-! # A1: saturation bases package for c0Q-lattice vs lambda-lattice -/
noncomputable section
open Module
namespace LeanFormal.IUT.XiFPaper.Mzk1A1SaturationBasesActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeCompareActual
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1SaturationBasesDataActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]

theorem closure_c0Q_le_closure_lambda :
    AddSubgroup.closure (c0QLattice T b) ≤ AddSubgroup.closure (lambdaLattice T b) :=
  AddSubgroup.closure_mono (c0QLattice_subset_lambdaLattice T b)

/-- A1 saturation bases package: only the two integral bases are input. -/
noncomputable def a1SaturationBasesData
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b₁ : Module.Basis ι ℤ (AddSubgroup.closure (c0QLattice T b)).toIntSubmodule)
    (b₂ : Module.Basis ι ℤ (AddSubgroup.closure (lambdaLattice T b)).toIntSubmodule)
    (hne : (AddSubgroup.closure (c0QLattice T b)).relIndex
      (AddSubgroup.closure (lambdaLattice T b)) ≠ 0) :
    SaturationBasesData (rootNormedExtension T b) where
  L₁ := AddSubgroup.closure (c0QLattice T b)
  L₂ := AddSubgroup.closure (lambdaLattice T b)
  le := closure_c0Q_le_closure_lambda T b
  ι := ι
  b₁ := b₁
  b₂ := b₂
  relIndex_ne_zero := hne

end LeanFormal.IUT.XiFPaper.Mzk1A1SaturationBasesActual
