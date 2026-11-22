/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A1LatticeCompareActual
import tmp.sheaf.xif.paper.Mzk1PadicSaturationBasesActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.Tactic

/-! # A1: p-adic saturation bases for c0Q/lambda lattices -/
noncomputable section
open Module
namespace LeanFormal.IUT.XiFPaper.Mzk1A1PadicSaturationBasesActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeCompareActual
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1PadicSaturationBasesActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
variable (p : ℕ) [Fact p.Prime]

variable [Module ℤ_[p] (rootNormedExtension T b)]

theorem span_c0Q_le_span_lambda :
    Submodule.span ℤ_[p] (c0QLattice T b) ≤ Submodule.span ℤ_[p] (lambdaLattice T b) :=
  Submodule.span_mono (c0QLattice_subset_lambdaLattice T b)

/-- Stage4 p-adic package: only the two Z_p-bases are input. -/
noncomputable def a1PadicSaturationBasesData
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b₁ : Module.Basis ι ℤ_[p] (Submodule.span ℤ_[p] (c0QLattice T b)))
    (b₂ : Module.Basis ι ℤ_[p] (Submodule.span ℤ_[p] (lambdaLattice T b)))
    (hne : (Submodule.span ℤ_[p] (c0QLattice T b)).toAddSubgroup.relIndex
      (Submodule.span ℤ_[p] (lambdaLattice T b)).toAddSubgroup ≠ 0) :
    PadicSaturationBasesData p (rootNormedExtension T b) where
  L₁ := Submodule.span ℤ_[p] (c0QLattice T b)
  L₂ := Submodule.span ℤ_[p] (lambdaLattice T b)
  le := span_c0Q_le_span_lambda T b p
  ι := ι
  b₁ := b₁
  b₂ := b₂
  relIndex_ne_zero := hne

end LeanFormal.IUT.XiFPaper.Mzk1A1PadicSaturationBasesActual
