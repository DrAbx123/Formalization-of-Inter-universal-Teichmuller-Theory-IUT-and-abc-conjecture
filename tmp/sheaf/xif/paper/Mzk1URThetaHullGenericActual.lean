/- U-R C2 theta-upper: generic (abstract place/tuple) hull lemmas.

Route-compliant new glue at the abstract tensor-block level (no concrete packet
instances, to avoid elaboration blow-ups): a scaled region with nonnegative
coefficients is contained in O_hol, and the theta hull of the actual coefficient
family (label j coefficient gaussExponent j * c1, including label 0) equals
O_hol.  The concrete packet corollaries are instantiated in
Mzk1URThetaHullTensorActual.

Accepted layer used: arithmeticTupleFractionalLattice_mono,
arithmeticTupleFractionalLattice_zero,
arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice,
coefficient_arithmeticTupleHolomorphicLattice,
arithmeticTupleNormalizedLogVolume_canonicalUnitReference. -/
import tmp.sheaf.xif.paper.Mzk1URThetaHullUpperActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaHullGenericActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open MeasureTheory

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable {l : PrimeGeFive}

/-- The actual theta coefficient family with base coefficient c1. -/
def thetaCoefficientFamily (c1 : ℝ) : SignedLabel l.value → ι → ℝ :=
  fun j _ => (gaussExponent j.1).toNat * c1

/-- A scaled region with nonnegative coefficient vector lies in O_hol. -/
theorem fractionalLattice_mul_holomorphic_le (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    arithmeticTupleFractionalLattice places tuple c *
        arithmeticTupleHolomorphicLattice places tuple ≤
      arithmeticTupleHolomorphicLattice places tuple := by
  have hmono : arithmeticTupleFractionalLattice places tuple c ≤
      arithmeticTupleFractionalLattice places tuple (fun _ => 0) :=
    arithmeticTupleFractionalLattice_mono
      (places := places) (tuple := tuple) (a := fun _ => 0) (b := c)
      (fun i => hc i)
  calc arithmeticTupleFractionalLattice places tuple c *
        arithmeticTupleHolomorphicLattice places tuple
      ≤ arithmeticTupleFractionalLattice places tuple (fun _ => 0) *
          arithmeticTupleHolomorphicLattice places tuple := mul_le_mul' hmono le_rfl
    _ = arithmeticTupleValuationIntegerLattice places tuple *
          arithmeticTupleHolomorphicLattice places tuple := by
        rw [arithmeticTupleFractionalLattice_zero]
    _ = arithmeticTupleHolomorphicLattice places tuple :=
        arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice places tuple

/-- The zero label in SignedLabel. -/
def thetaZeroLabel : SignedLabel l.value :=
  ⟨0, by
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · exact neg_nonpos.mpr (Int.natCast_nonneg _)
    · exact Int.natCast_nonneg _⟩

/-- The zero-label scaled region is O_hol itself. -/
theorem thetaRegion_zero_eq_holomorphic (c1 : ℝ) :
    thetaTensorScaledRegion places tuple
        (thetaCoefficientFamily (ι := ι) (l := l) c1 thetaZeroLabel) =
      (arithmeticTupleHolomorphicLattice places tuple :
        Set (ArithmeticTensorTupleBlock places tuple)) := by
  rw [thetaTensorScaledRegion]
  have hcoef : thetaCoefficientFamily (ι := ι) (l := l) c1 (thetaZeroLabel (l := l)) =
      (fun _ => (0 : ℝ)) := by
    funext i
    simp [thetaCoefficientFamily, thetaZeroLabel, gaussExponent]
  rw [hcoef]
  have hmul : arithmeticTupleFractionalLattice places tuple (fun _ => 0) *
      arithmeticTupleHolomorphicLattice places tuple =
      arithmeticTupleHolomorphicLattice places tuple := by
    rw [arithmeticTupleFractionalLattice_zero]
    exact arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice places tuple
  exact congrArg (fun S : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple) =>
    (S : Set (ArithmeticTensorTupleBlock places tuple))) hmul

/-- Every label region (c1 >= 0) is contained in O_hol. -/
theorem thetaRegion_subset_holomorphic (c1 : ℝ) (hc1 : 0 ≤ c1)
    (j : SignedLabel l.value) :
    thetaTensorScaledRegion places tuple
        (thetaCoefficientFamily (ι := ι) (l := l) c1 j) ⊆
      (arithmeticTupleHolomorphicLattice places tuple :
        Set (ArithmeticTensorTupleBlock places tuple)) := by
  intro x hx
  rw [thetaTensorScaledRegion] at hx
  have hc : ∀ i, 0 ≤ thetaCoefficientFamily (ι := ι) (l := l) c1 j i :=
    fun i => mul_nonneg (Nat.cast_nonneg _) hc1
  exact fractionalLattice_mul_holomorphic_le places tuple
    (thetaCoefficientFamily (ι := ι) (l := l) c1 j) hc hx

/-- The theta image set is contained in O_hol. -/
theorem thetaImageSet_subset_holomorphic (c1 : ℝ) (hc1 : 0 ≤ c1) :
    (⋃ j : SignedLabel l.value,
        thetaTensorScaledRegion places tuple
          (thetaCoefficientFamily (ι := ι) (l := l) c1 j)) ⊆
      (arithmeticTupleHolomorphicLattice places tuple :
        Set (ArithmeticTensorTupleBlock places tuple)) := by
  intro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  exact thetaRegion_subset_holomorphic places tuple c1 hc1 j hj

#print axioms fractionalLattice_mul_holomorphic_le
#print axioms thetaRegion_zero_eq_holomorphic
#print axioms thetaRegion_subset_holomorphic
#print axioms thetaImageSet_subset_holomorphic

end LeanFormal.IUT.XiFPaper.Mzk1URThetaHullGenericActual
end