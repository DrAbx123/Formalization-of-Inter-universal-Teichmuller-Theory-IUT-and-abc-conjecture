/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1QPilotPlaceDegreeActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36ProductFormula
import Mathlib.Tactic

/-! # R29u / task-101: explicit divisor from bad places (single-place construction) -/

/-
| field | value |
|---|---|
| Status | PARTIAL/green: real `ExplicitDivisor F` constructed from one bad place (Finsupp single at HeightOneSpectrum of `qVFamTensorPlace`, coefficient = order, arch 0); weight identity proved under the cardinality bridge hypothesis |
| Reuse | `QVFamTensorCoefficientActual:47/51/76`; `Example36ProductFormula:313 globalPrimeStripWeight`; `Mzk1QPilotPlaceDegreeActual: nativeBadPlace_abs_log_eq` |
| GAP | GAP-DEGREE-CARD: `finitePlaceResidueCardinality (heightOne place) = residueNormBase place` not proved here (explicit `hcard` hypothesis); this is the height-one-spectrum vs FinitePlace residue-cardinality bridge |
| GAP | GAP-DEGREE-SUM: the full `nativeBadValuationSum` (sum over all bad places) needs the Finsupp sum-additivity construction (sum of `Finsupp.single`); single-place block is done |
| 纪律 | no sorry/axiom; construction is real data (Finsupp.single), identification hypotheses explicit |
-/

noncomputable section
open scoped BigOperators NumberField
open IsDedekindDomain NumberField

namespace LeanFormal.IUT.XiFPaper.Mzk1DegreeExplicitActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PrimeStripProductFormula
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotPlaceDegreeActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. Bad place → height-one spectrum -/

/-- The actual height-one spectrum of a bad place, via the F-place map. -/
noncomputable def nativeBadHeightOne (b : Bad (nativePlaceSelection T)) :
    HeightOneSpectrum (𝓞 T.arithmetic.F) :=
  (NumberField.FinitePlace.equivHeightOneSpectrum).toFun (qVFamTensorPlace T b)

/-- The integer coefficient of the explicit divisor at a bad place (the q order). -/
noncomputable def nativeBadIntCoeff (b : Bad (nativePlaceSelection T)) : ℤ :=
  ((qVFamily T b).order : ℤ)

/-! ## 2. Single-place explicit divisor and its weight -/

/-- The actual explicit divisor supported on one bad place: finite coefficient `order_b`,
archimedean part zero. -/
noncomputable def nativeBadExplicitDivisor (b : Bad (nativePlaceSelection T)) :
    SourceModelBackend.ExplicitDivisor T.arithmetic.F :=
  (Finsupp.single (nativeBadHeightOne T b) (nativeBadIntCoeff T b), fun _ => 0)

/-- The integer coefficient casts to the real qVFam coefficient. -/
theorem nativeBadIntCoeff_cast (b : Bad (nativePlaceSelection T)) :
    ((nativeBadIntCoeff T b : ℤ) : ℝ) = qVFamTensorCoefficient T b := by
  unfold nativeBadIntCoeff
  rw [qVFamTensorCoefficient_eq_order]
  push_cast
  ring

/-- **Weight identity (single place)**: the Example36 degree of the explicit divisor is
`order_b * log(residueNormBase place_b)`, under the residue-cardinality bridge. -/
theorem globalPrimeStripWeight_nativeBadExplicitDivisor
    (b : Bad (nativePlaceSelection T))
    (hcard : (finitePlaceResidueCardinality (F := T.arithmetic.F)
        (nativeBadHeightOne T b) : ℝ) =
      residueNormBase (qVFamTensorPlace T b)) :
    globalPrimeStripWeight (F := T.arithmetic.F) (nativeBadExplicitDivisor T b) =
      qVFamTensorCoefficient T b * Real.log (residueNormBase (qVFamTensorPlace T b)) := by
  unfold globalPrimeStripWeight nativeBadExplicitDivisor
  rw [Finsupp.sum_single_index]
  · simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    rw [nativeBadIntCoeff_cast, hcard]
  · simp

/-- Combining with the per-place valuation equality: the Example36 degree of the
single-place explicit divisor equals `|log ‖q_b‖|`. -/
theorem globalPrimeStripWeight_nativeBadExplicitDivisor_eq_abs_log
    (b : Bad (nativePlaceSelection T))
    (hcard : (finitePlaceResidueCardinality (F := T.arithmetic.F)
        (nativeBadHeightOne T b) : ℝ) =
      residueNormBase (qVFamTensorPlace T b)) :
    globalPrimeStripWeight (F := T.arithmetic.F) (nativeBadExplicitDivisor T b) =
      |Real.log (qVFamDefaultNorm T b)| := by
  rw [globalPrimeStripWeight_nativeBadExplicitDivisor (T := T) (b := b) hcard]
  exact (nativeBadPlace_abs_log_eq (T := T) (b := b)).symm

def degreeExplicitRows : List (String × String) :=
  [ ("nativeBadHeightOne", "actual HeightOneSpectrum map (via qVFamTensorPlace)") ,
    ("nativeBadExplicitDivisor", "real Finsupp.single divisor, arch 0") ,
    ("nativeBadIntCoeff_cast", "integer order coefficient casts to qVFam TensorCoefficient (PROVED)") ,
    ("globalPrimeStripWeight_nativeBadExplicitDivisor", "weight = order*log residueNormBase (hcard)") ,
    ("globalPrimeStripWeight_nativeBadExplicitDivisor_eq_abs_log", "weight = |log||q_b||| (hcard)") ,
    ("GAP-DEGREE-CARD", "finitePlaceResidueCardinality = residueNormBase bridge missing") ,
    ("GAP-DEGREE-SUM", "full sum over bad places (Finsupp sum additivity) missing") ]

theorem degreeExplicitRows_length : degreeExplicitRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DegreeExplicitActual