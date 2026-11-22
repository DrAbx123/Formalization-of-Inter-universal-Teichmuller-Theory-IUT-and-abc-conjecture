import tmp.sheaf.xif.paper.Mzk1A1LatticeCompareActual
import tmp.sheaf.xif.paper.Mzk1PadicSaturationBasesActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
/-! #A1: actual K/F lattices as Z_p-submodules, replacing the Z-basis version.
The two lattices are the Z_p-spans of the actual qhat-lattice and lambda-lattice;
only the Z_p-integral bases and the nonzero relative index are input. -/
noncomputable section
open Module
namespace LeanFormal.IUT.XiFPaper.Mzk1A1PadicSaturationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeCompareActual
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1PadicSaturationBasesActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Actual qhat-lattice as a Z_p-submodule. -/
noncomputable def c0QPadicLattice :
    Submodule ℤ_[qVFamTensorP T b] (rootNormedExtension T b) :=
  Submodule.span ℤ_[qVFamTensorP T b] (c0QLattice T b)
/-- Actual lambda-lattice as a Z_p-submodule. -/
noncomputable def lambdaPadicLattice :
    Submodule ℤ_[qVFamTensorP T b] (rootNormedExtension T b) :=
  Submodule.span ℤ_[qVFamTensorP T b] (lambdaLattice T b)
/-- A1.4 at the Z_p-lattice level. -/
theorem c0QPadicLattice_le_lambdaPadicLattice :
    c0QPadicLattice T b ≤ lambdaPadicLattice T b := by
  unfold c0QPadicLattice lambdaPadicLattice
  exact Submodule.span_mono (c0QLattice_subset_lambdaLattice T b)
/-- Replace the Z-basis interface by the Z_p-basis one: only bases and a nonzero
relative index are needed. -/
noncomputable def a1PadicSaturationBasesData
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b₁ : Module.Basis ι ℤ_[qVFamTensorP T b] (c0QPadicLattice T b))
    (b₂ : Module.Basis ι ℤ_[qVFamTensorP T b] (lambdaPadicLattice T b))
    (hne : (c0QPadicLattice T b).toAddSubgroup.relIndex
      (lambdaPadicLattice T b).toAddSubgroup ≠ 0) :
    PadicSaturationBasesData (qVFamTensorP T b) (rootNormedExtension T b) where
  L₁ := c0QPadicLattice T b
  L₂ := lambdaPadicLattice T b
  le := c0QPadicLattice_le_lambdaPadicLattice T b
  ι := ι
  b₁ := b₁
  b₂ := b₂
  relIndex_ne_zero := hne
end LeanFormal.IUT.XiFPaper.Mzk1A1PadicSaturationActual
end