import tmp.sheaf.xif.paper.Mzk1P0LReadoutEqNativeActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNativeLSideBridgeActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutEqNativeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
structure NativeLSideBridge (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  readout : LReadoutEqNative I place T b
  theta_nonneg : 0 ≤ thetaReadActual I place
def NativeLSideBridgeRequired (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (NativeLSideBridge I place T b)
end LeanFormal.IUT.XiFPaper.Mzk1P0LNativeLSideBridgeActual