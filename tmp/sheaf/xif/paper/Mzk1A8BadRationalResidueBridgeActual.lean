import tmp.sheaf.xif.paper.Mzk1PaperLabelBadIndexBridgeActual
import tmp.sheaf.xif.paper.Mzk1PaperLabelProjectionActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.Mzk1PrimePlaceAbsNormActual
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A8BadRationalResidueBridgeActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1PaperLabelProjectionActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperLabelBadIndexBridgeActual

variable {K : Type} [Field K] [NumberField K]

/-- `rationalPrimeOfFinitePlace` at the maximal ideal is the residue characteristic;
this is the `Ideal.ringChar_quot` bridge. -/
theorem rationalPrimeOfFinitePlace_maximalIdeal_eq_residueCharacteristic
    (place : NumberField.FinitePlace K) :
    rationalPrimeOfFinitePlace K place.maximalIdeal =
      NumberFieldFinitePlace.residueCharacteristic place := by
  unfold rationalPrimeOfFinitePlace rationalPrimeIdealOfFinitePlace
  unfold NumberFieldFinitePlace.residueCharacteristic NumberFieldFinitePlace.ResidueField
  rw [Ideal.ringChar_quot]

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual bridge: the bad rational prime is exactly the residue characteristic
of the bad place. -/
theorem badRationalPrime_eq_residueCharacteristic
    (b : Bad (nativePlaceSelection T)) :
    badRationalPrime T b =
      NumberFieldFinitePlace.residueCharacteristic b.1 := by
  unfold badRationalPrime
  rw [rationalPrimeOfFinitePlace_maximalIdeal_eq_residueCharacteristic]
  rw [← nativeBadToKPlace_comap (T := T) b]
  exact (residueCharacteristic_comap (k := T.arithmetic.Fmod)
    (nativeBadToKPlace T b)).symm

#print axioms rationalPrimeOfFinitePlace_maximalIdeal_eq_residueCharacteristic
#print axioms badRationalPrime_eq_residueCharacteristic
end LeanFormal.IUT.XiFPaper.Mzk1A8BadRationalResidueBridgeActual