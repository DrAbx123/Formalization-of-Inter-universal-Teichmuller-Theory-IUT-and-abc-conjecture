import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Default-norm Completion tensor block: actual qVFamily data and API gap

The existing ArithmeticTensorTupleBlock uses CommonPrimeCompletion with the
normalized spectral norm.  The default completion norm is the valuation norm on
Completion(place).

This file constructs the actual default-norm qVFamily generator q and the actual
full coefficient

  c_full = -logb_p ||q||,

and proves ||q|| = p^(-c_full).  This is the actual c_full generator data.

The tensor carrier of FinitePadicTensor requires, by its file's typeclass
variables, NormedAddCommGroup and NormedSpace ℚ_[p] on each factor.  The
default completion has its valuation norm and an Algebra ℚ_[p] structure, but
no NormedSpace ℚ_[p] instance compatible with that default norm (only the
normalized completion has the normalized spectral norm).  Therefore the
default-norm tensor block, tensor integral region, tensor norm and Haar are
not constructed; the exact missing API is recorded as a Prop, not faked.

No fake block/norm/Haar; no sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.DefaultNormTensorBlockActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.LocalFieldPadicTensor

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual default-norm completion place. -/
abbrev defaultNormPlace : NumberField.FinitePlace T.arithmetic.F :=
  (nativeBadLift T).lift b

/-- The actual rational prime of the default-norm place. -/
noncomputable def defaultNormP : ℕ :=
  qVFamTensorP T b

/-- The default-norm prime is prime. -/
noncomputable instance defaultNormPFact
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) :
    Fact (Nat.Prime (defaultNormP T b)) := by
  unfold defaultNormP
  infer_instance

/-- The actual qVFamily completion generator (default norm). -/
noncomputable def defaultNormGenerator
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) :
    Completion (defaultNormPlace T b) :=
  (qVFamily T b).q

/-- The actual full coefficient c_full = -logb_p ||q||. -/
noncomputable def defaultNormFullCoefficient
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Real :=
  -Real.logb (defaultNormP T b : Real) ‖defaultNormGenerator T b‖

/-- Actual norm relation: ||q|| = p^(-c_full). -/
theorem defaultNormGenerator_norm
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) :
    ‖defaultNormGenerator T b‖ =
      (defaultNormP T b : Real) ^ (-(defaultNormFullCoefficient T b)) := by
  unfold defaultNormGenerator defaultNormFullCoefficient defaultNormP
  have hp_pos : (0 : Real) < (qVFamTensorP T b : Real) := by
    have hprime : Nat.Prime (qVFamTensorP T b) := by
      unfold qVFamTensorP
      exact (completionRationalPrime (qVFamTensorPlace T b)).property
    exact_mod_cast hprime.pos
  have hp_ne_one : (qVFamTensorP T b : Real) ≠ 1 := by
    have hprime : Nat.Prime (qVFamTensorP T b) := by
      unfold qVFamTensorP
      exact (completionRationalPrime (qVFamTensorPlace T b)).property
    exact ne_of_gt (by exact_mod_cast hprime.one_lt : (1 : Real) < (qVFamTensorP T b : Real))
  have hnorm_pos : 0 < ‖(qVFamily T b).q‖ :=
    norm_pos_iff.mpr (qVFamily T b).q_ne_zero
  rw [neg_neg]
  exact (Real.rpow_logb hp_pos hp_ne_one hnorm_pos).symm

/-- Exact missing API: NormedSpace ℚ_[p] on the default completion compatible
with its default valuation norm.  This is not asserted. -/
def DefaultNormNormedSpaceRequired
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (NormedSpace ℚ_[(defaultNormP T b)] (Completion (defaultNormPlace T b)))

/-- Exact missing API: a default-norm tensor carrier with tensor norm, integral
region and Haar.  It needs the missing NormedSpace instance above, since
FinitePadicTensor is parameterized by normed Qp-modules. -/
structure DefaultNormTensorBlockRequired
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) where
  normedSpace : Prop
  normedSpace_eq : normedSpace = DefaultNormNormedSpaceRequired T b
  tensorCarrier : Prop
  tensorIntegralRegion : Prop
  tensorHaar : Prop
  tensorScaling : Prop

/-- Actual default-norm generator data, with the exact tensor-block API gap
recorded as a Prop (not asserted). -/
structure DefaultNormGeneratorData
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) where
  generator : Completion (defaultNormPlace T b)
  generator_eq : generator = defaultNormGenerator T b
  coefficient : Real
  coefficient_eq : coefficient = defaultNormFullCoefficient T b
  generator_norm : ‖generator‖ = (defaultNormP T b : Real) ^ (-coefficient)
  tensorBlockRequired : Prop
  tensorBlockRequired_eq : tensorBlockRequired =
    Nonempty (DefaultNormTensorBlockRequired T b)

/-- The actual default-norm generator data constructor. -/
noncomputable def defaultNormGeneratorData :
    DefaultNormGeneratorData T b where
  generator := defaultNormGenerator T b
  generator_eq := rfl
  coefficient := defaultNormFullCoefficient T b
  coefficient_eq := rfl
  generator_norm := defaultNormGenerator_norm T b
  tensorBlockRequired := Nonempty (DefaultNormTensorBlockRequired T b)
  tensorBlockRequired_eq := rfl

end LeanFormal.IUT.XiFPaper.DefaultNormTensorBlockActual

end
