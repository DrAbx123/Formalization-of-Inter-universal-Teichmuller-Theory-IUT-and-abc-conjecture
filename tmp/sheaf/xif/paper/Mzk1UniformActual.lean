import tmp.sheaf.xif.paper.Mzk1ValueGroupProofActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1GaloisCompletionActual
open LeanFormal.IUT.XiFPaper.Mzk1GaloisToMZActual
open LeanFormal.IUT.XiFPaper.Mzk1ValueGroupActual
open LeanFormal.IUT.XiFPaper.Mzk1ValueGroupProofActual
open LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual

namespace LeanFormal.IUT.XiFPaper.Mzk1UniformActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
variable (v : NumberField.FinitePlace T.arithmetic.F)

/-- Exact remaining interface for the target-basis uniform-continuity argument:
the unit transfer between the two ValueGroup₀'s has not been constructed yet. -/
structure UniformContinuitySource where
  is_uniformContinuous : UniformContinuous (withValMovedSigma (T := T) σ v)

end LeanFormal.IUT.XiFPaper.Mzk1UniformActual
end
