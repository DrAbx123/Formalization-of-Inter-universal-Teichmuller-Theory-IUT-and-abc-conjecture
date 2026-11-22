import tmp.sheaf.xif.paper.S923RInteriorNonemptyActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicSubmoduleTensor
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
/-! # S1015: openness of the paper fractional lattice F(cRoot)
Local fractional lattices are nonzero-radius closed balls, hence open in the
ultrametric field.  Tensor-span openness reduces to the exact local span-top
and finite-module inputs. -/
noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000
namespace LeanFormal.IUT.XiFPaper.S1015FractionalLatticeOpenActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
theorem isOpen_padicFractionalLattice (p : Nat) [Fact p.Prime]
    (K : Type u) [NormedField K] [IsUltrametricDist K]
    [NormedAlgebra ℚ_[p] K] (a : Real) :
    IsOpen (padicFractionalLattice (p := p) (K := K) a : Set K) := by
  have hset : (padicFractionalLattice (p := p) (K := K) a : Set K) =
      Metric.closedBall (0 : K) ((p : Real) ^ (-a)) := by
    ext x
    change x ∈ padicFractionalLattice (p := p) (K := K) a ↔
      x ∈ Metric.closedBall (0 : K) ((p : Real) ^ (-a))
    rw [mem_padicFractionalLattice_iff, Metric.mem_closedBall, dist_zero_right]
  rw [hset]
  have hp : (0 : Real) < (p : Real) := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  exact IsUltrametricDist.isOpen_closedBall (0 : K)
    (Real.rpow_pos_of_pos hp _).ne'
theorem s923FractionalLatticeOpen_of_spanTop
    (h : ∀ i : qVFamTensorV,
      Submodule.span ℚ_[(qVFamTensorP T b)]
        (padicFractionalLattice (p := qVFamTensorP T b)
          (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
          (paperRootCoefficientFamily (l := l) T b i) :
            Set (CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))) = ⊤) :
    S923FractionalLatticeOpen (l := l) T b := by
  unfold S923FractionalLatticeOpen s923F arithmeticTupleFractionalLattice
  haveI : ∀ i : qVFamTensorV, Module.Finite ℤ_[(qVFamTensorP T b)]
      (padicFractionalLattice (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
        (paperRootCoefficientFamily (l := l) T b i)) := fun i =>
    finite_padicFractionalLattice_of_nonneg
      (p := qVFamTensorP T b)
      (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
      (paperRootCoefficientFamily (l := l) T b i)
      (paperRootCoefficientFamily_nonneg (l := l) T b i)
  haveI : ∀ i : qVFamTensorV, Module.Free ℤ_[(qVFamTensorP T b)]
      (padicFractionalLattice (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
        (paperRootCoefficientFamily (l := l) T b i)) := fun i =>
    free_padicFractionalLattice_of_nonneg
      (p := qVFamTensorP T b)
      (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
      (paperRootCoefficientFamily (l := l) T b i)
      (paperRootCoefficientFamily_nonneg (l := l) T b i)
  exact isOpen_submoduleTensorSpan (p := qVFamTensorP T b)
    (M := fun i : qVFamTensorV =>
      CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
    (S := fun i : qVFamTensorV =>
      padicFractionalLattice (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
        (paperRootCoefficientFamily (l := l) T b i)) h
end LeanFormal.IUT.XiFPaper.S1015FractionalLatticeOpenActual
