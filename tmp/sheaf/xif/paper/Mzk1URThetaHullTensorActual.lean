/- U-R C2 theta-upper, tensor lifting stage 1: tensor-lattice congruence and the
region nesting towards the value-group ceiling (singleCoordinate route).

Route-compliant new glue (definitions only): congruence of the fractional tensor
lattice under pointwise equality of the local norm balls; the identification of
the constant coefficient family with the single-coordinate family when the index
type is a subsingleton; and the resulting nesting of the actual theta regions
into the single-coordinate ceiling container.

Used accepted layer: arithmeticTupleFractionalLattice / submoduleTensorSpan /
tensorIntegralRegion definitions (FinitePlaceFractionalTensorLattice), the
monotonicity donor arithmeticTupleFractionalLattice_mono, and the new local
ball-ceil equality padicFractionalLattice_eq_intCeil
(Mzk1URThetaHullUpperActual, proved). -/
import tmp.sheaf.xif.paper.Mzk1URThetaHullUpperActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullGenericActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaHullTensorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullUpperActual
open MeasureTheory

universe u v w

/-! ## Stage 1a: tensor-lattice congruence (definitions only) -/

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

/-- Congruence of the fractional tensor lattice under pointwise equality of the
local fractional (norm ball) lattices. -/
theorem arithmeticTupleFractionalLattice_congr {a b : ι → ℝ}
    (h : ∀ i, padicFractionalLattice (p := p)
        (K := CommonPrimeCompletion (places i (tuple i))) (a i) =
      padicFractionalLattice (p := p)
        (K := CommonPrimeCompletion (places i (tuple i))) (b i)) :
    arithmeticTupleFractionalLattice places tuple a =
      arithmeticTupleFractionalLattice places tuple b := by
  have hfun : (fun i => padicFractionalLattice (p := p)
        (K := CommonPrimeCompletion (places i (tuple i))) (a i)) =
      (fun i => padicFractionalLattice (p := p)
        (K := CommonPrimeCompletion (places i (tuple i))) (b i)) :=
    funext (fun i => h i)
  unfold arithmeticTupleFractionalLattice
  rw [hfun]

/-- On a subsingleton index type the constant coefficient family is the
single-coordinate coefficient family. -/
theorem arithmeticTupleFractionalLattice_const_eq_single [Subsingleton ι]
    (iSelected : ι) (mu : ℝ) :
    arithmeticTupleFractionalLattice places tuple (fun _ => mu) =
      arithmeticTupleSingleFractionalLattice places tuple iSelected mu := by
  unfold arithmeticTupleSingleFractionalLattice
  apply arithmeticTupleFractionalLattice_congr
  intro i
  unfold arithmeticTupleSingleFractionalExponent
  rw [if_pos (Subsingleton.elim i iSelected)]

/-! ## Stage 1b: the actual theta regions nest into the ceiling container -/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The value-group ceiling of a real coefficient at the actual packet factor. -/
noncomputable def urCeilCoeff (c : ℝ) : ℝ :=
  ceilExp (p := qVFamTensorP T b)
    (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) () ())) c

/-- The actual root coefficient is nonnegative. -/
theorem urRootCoeff_nonneg : 0 ≤ actualRootCoeff (l := l) T b () := by
  unfold actualRootCoeff
  exact div_nonneg (qVFamNormalizedCoefficient_nonneg T b) (by positivity)

/-- The ceiling coefficient is at least the coefficient. -/
theorem urCeilCoeff_ge {c : ℝ} (hc : 0 ≤ c) : c ≤ urCeilCoeff (l := l) T b c :=
  le_ceilExp (p := qVFamTensorP T b)
    (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) () ())) hc

/-- The local ball-ceil equality applies at the actual packet factor. -/
theorem urLocal_ball_eq_ceil (c : ℝ) (hc : 0 ≤ c) :
    padicFractionalLattice (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) () ())) c =
      padicFractionalLattice (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) () ()))
        (urCeilCoeff (l := l) T b c) := by
  unfold urCeilCoeff
  exact padicFractionalLattice_eq_intCeil (p := qVFamTensorP T b) hc




#print axioms arithmeticTupleFractionalLattice_congr
#print axioms arithmeticTupleFractionalLattice_const_eq_single
#print axioms urRootCoeff_nonneg
#print axioms urCeilCoeff_ge
#print axioms urLocal_ball_eq_ceil

end LeanFormal.IUT.XiFPaper.Mzk1URThetaHullTensorActual
end