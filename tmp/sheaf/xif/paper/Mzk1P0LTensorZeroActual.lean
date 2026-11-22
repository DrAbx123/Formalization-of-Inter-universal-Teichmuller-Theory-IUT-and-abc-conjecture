import tmp.sheaf.xif.paper.Mzk1P0LRegionNonemptyActual
/-! CONSUMER RE-EXPORT — re-exports an existing theorem; not a new proof. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LTensorZeroActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LRegionNonemptyActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem tensor_zero_mem := zero_mem_thetaRegion I place
end LeanFormal.IUT.XiFPaper.Mzk1P0LTensorZeroActual