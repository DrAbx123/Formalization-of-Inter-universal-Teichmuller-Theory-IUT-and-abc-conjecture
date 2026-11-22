/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DegreeExplicitActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36ProductFormula
import Mathlib.Tactic

/-! # R29y / task-105: full bad-index ExplicitDivisor sum and residue-cardinality bridge -/

/-
| field | value |
|---|---|
| Status | green attempt: GAP-DEGREE-CARD closed; full bad-index Finsupp construction and weight = nativeBadQAbsLogSum |
| Reuse | `Mzk1DegreeExplicitActual` (single place), `Mzk1QPilotPlaceDegreeActual` (nativeBadQAbsLogSum_eq_valuationSum), `QVFamTensorCoefficientActual`, `Example36ProductFormula:313` |
| GAP | linking the native degree to a contract `I`/`S` sourceBadQAbsLog remains GAP-SOURCE-NATIVE-Q (Mzk1QPilotPlaceDegreeActual §4) |
| 纪律 | no sorry/axiom; nonzero real construction, no Prop placeholder |
-/

noncomputable section
open scoped BigOperators NumberField
open IsDedekindDomain NumberField

namespace LeanFormal.IUT.XiFPaper.Mzk1DegreeSumActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PrimeStripProductFormula
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotPlaceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1DegreeExplicitActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. GAP-DEGREE-CARD: residue-cardinality bridge -/

/-- **GAP-DEGREE-CARD closed**: the residue-field cardinality at the height-one
spectrum of a bad place equals the real residue norm base at the corresponding F-place. -/
theorem finitePlaceResidueCardinality_nativeBadHeightOne
    (b : Bad (nativePlaceSelection T)) :
    (finitePlaceResidueCardinality (F := T.arithmetic.F)
        (nativeBadHeightOne T b) : ℝ) =
      residueNormBase (qVFamTensorPlace T b) := by
  unfold nativeBadHeightOne finitePlaceResidueCardinality residueNormBase
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

/-! ## 2. Full bad-index Finsupp construction -/

/-- The full bad-index finite divisor: sum of single-point Finsupps over the bad index. -/
noncomputable def nativeBadFiniteDivisor :
    HeightOneSpectrum (𝓞 T.arithmetic.F) →₀ ℤ :=
  ∑ b : Bad (nativePlaceSelection T),
    Finsupp.single (nativeBadHeightOne T b) (nativeBadIntCoeff T b)

/-- The full explicit divisor: finite part from the bad index, archimedean part zero. -/
noncomputable def nativeBadExplicitDivisorSum :
    SourceModelBackend.ExplicitDivisor T.arithmetic.F :=
  (nativeBadFiniteDivisor T, fun _ => 0)

/-! ## 3. Weight of the full sum -/

/-- Sum-additivity of `Finsupp.sum` over a Finset of single-point Finsupps. -/
theorem nativeBadFiniteDivisor_sum_weight :
    (nativeBadFiniteDivisor T).sum
        (fun v n => (n : ℝ) *
          Real.log (finitePlaceResidueCardinality (F := T.arithmetic.F) v)) =
      ∑ b : Bad (nativePlaceSelection T),
        (nativeBadIntCoeff T b : ℝ) *
          Real.log (finitePlaceResidueCardinality (F := T.arithmetic.F)
            (nativeBadHeightOne T b)) := by
  classical
  unfold nativeBadFiniteDivisor
  induction (Finset.univ : Finset (Bad (nativePlaceSelection T))) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [Finsupp.sum_add_index' (fun v => by simp) (fun v x y => by push_cast; ring)]
      rw [Finsupp.sum_single_index]
      · rw [ih, Finset.sum_insert ha]
      · simp

/-- **Full weight identity**: Example36 degree of the full bad-index explicit divisor equals
the native valuation sum. -/
theorem globalPrimeStripWeight_nativeBadExplicitDivisorSum :
    globalPrimeStripWeight (F := T.arithmetic.F) (nativeBadExplicitDivisorSum T) =
      nativeBadValuationSum T := by
  unfold globalPrimeStripWeight nativeBadExplicitDivisorSum nativeBadValuationSum
  rw [nativeBadFiniteDivisor_sum_weight]
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro b _
  rw [nativeBadIntCoeff_cast, finitePlaceResidueCardinality_nativeBadHeightOne]

/-- **Full bridge to the native absolute-log sum** (task-99): the Example36 degree of the
full explicit divisor is `nativeBadQAbsLogSum`. -/
theorem globalPrimeStripWeight_nativeBadExplicitDivisorSum_eq_absLogSum :
    globalPrimeStripWeight (F := T.arithmetic.F) (nativeBadExplicitDivisorSum T) =
      nativeBadQAbsLogSum T := by
  rw [globalPrimeStripWeight_nativeBadExplicitDivisorSum]
  exact (nativeBadQAbsLogSum_eq_valuationSum T).symm

def degreeSumRows : List (String × String) :=
  [ ("finitePlaceResidueCardinality_nativeBadHeightOne", "GAP-DEGREE-CARD closed") ,
    ("nativeBadFiniteDivisor", "full bad-index Finsupp sum construction") ,
    ("nativeBadExplicitDivisorSum", "ExplicitDivisor with arch 0") ,
    ("nativeBadFiniteDivisor_sum_weight", "Finsupp.sum of Finset.sum of singles (PROVED)") ,
    ("globalPrimeStripWeight_nativeBadExplicitDivisorSum", "weight = nativeBadValuationSum (PROVED)") ,
    ("globalPrimeStripWeight_nativeBadExplicitDivisorSum_eq_absLogSum", "weight = nativeBadQAbsLogSum (PROVED)") ,
    ("GAP-SOURCE-NATIVE-Q", "contract qParameter family vs native qVFamDefaultNorm (task-99 §4)") ]

theorem degreeSumRows_length : degreeSumRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DegreeSumActual