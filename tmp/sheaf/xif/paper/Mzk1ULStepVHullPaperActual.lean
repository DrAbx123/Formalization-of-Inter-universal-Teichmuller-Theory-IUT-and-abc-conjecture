/- U-C Step (viii) (beta): per-label Step(v) paper bound wrapper (kurt; item (i)).

GENERIC layer only (abstract places/tuple/prime), to keep elaboration light: the
wrapper is exactly the accepted donor
FinitePlaceStepVAssembly.arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound
(L814) with the different-order sum written as Mzk1URLabelDataActual.labelDifferentSum
and the exceptional sum as urStepVExcSum.  david instantiates it at the T-side
(qVFamTensorPlaces T b, qVFamTensorTuple) and supplies the retained K-side
Kummer representative varpi / Phi = p6Phi / e decomposition / exceptional data
in his LabelStepVHullData (NO INHABITANT; provenance: L814 varpi slot is K,
actual root is in L = K(root), and S342 proves no 2l-th root of q exists in K).

No sorry, no axiom; hpaper output shape:
  actualHullLog <= (-localNormOrder p varpi + labelDifferentSum + 1) * labelLogP p + exc. -/
import tmp.sheaf.xif.paper.Mzk1URLabelDataActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1ULStepVHullPaperActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual
open MeasureTheory

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

/-- The exceptional-index sum of the paper Step (v) bound. -/
noncomputable def urStepVExcSum (exceptional : Finset ι) : ℝ :=
  ∑ i ∈ exceptional, (3 + Real.log
    (logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ))

/-- **hpaper** (paper Step (v) bound, L814 shape) from the accepted hull donor. -/
theorem hV_of_L814_data [DecidableEq ι]
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j', NormedField (E j')] [∀ j', NormedAlgebra ℚ_[p] (E j')]
    [∀ j', FiniteDimensional ℚ_[p] (E j')] [∀ j', ProperSpace (E j')]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j' : J) → E j'))
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hvarpi_ne : varpi ≠ 0)
    (Phi : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hPhi_ne : Phi.Nonempty)
    (hPhi : ∀ φ ∈ Phi,
      ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
        φ u ∈ arithmeticTupleUnitLogLattice places tuple)
    (exceptional : Finset ι)
    (small_outside : ∀ i, i ∉ exceptional →
      logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2) :
    arithmeticTupleNormalizedLogVolume places tuple μ
        (arithmeticTupleHolomorphicHull places tuple e
          (arithmeticTupleStepVPossibleImages places tuple istar varpi Phi)) ≤
      (-localNormOrder p varpi + labelDifferentSum places tuple + 1) * labelLogP p +
        urStepVExcSum places tuple exceptional := by
  unfold urStepVExcSum
  exact arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound
    places tuple μ e istar varpi hvarpi_ne Phi hPhi_ne hPhi exceptional small_outside

#print axioms hV_of_L814_data

end LeanFormal.IUT.XiFPaper.Mzk1ULStepVHullPaperActual
end