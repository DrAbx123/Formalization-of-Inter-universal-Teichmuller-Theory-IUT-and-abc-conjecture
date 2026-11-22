import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.Foundations.Theta.GaussianKernel

/-! # Actual weighted Theta signed scalar

Minimal actual Theta-side scalar for the direct signed comparison with the
native q-pilot normalized signed log-volume.

For each bad place b and each procession label j in F_l^x = ProcessionLabel l,
the theta value is the actual q_v^(j^2) at the actual signed representative of
the F_l^x label:

  thetaValueFromQ T b (SignedLabel.representative l (j : ZMod l.value)).

The local signed theta log is the F_l^x procession average (cardinality l - 1)
of the (negative) log theta values.  The global weighted signed scalar is the
nativeBadLocalWeight-weighted sum over the actual bad places.

The direct signed target is

  weightedThetaSignedScalar >= nativeGlobalQPilotNormalizedSignedLogVolume,

i.e. the negative Theta magnitude is at least the negative q magnitude.  The
inequality is recorded as a target, not asserted.  No IQHullLogVolumeInterface,
no carrier equivalence, no normalization equality, no fake inequality.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperWeightedThetaSignedActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual real local q_v at a bad place. -/
noncomputable def weightedBaseQReal (b : Bad (nativePlaceSelection T)) : Real :=
  ‖(baseQ T b).q‖

/-- The actual local q_v is positive. -/
theorem weightedBaseQReal_pos (b : Bad (nativePlaceSelection T)) :
    0 < weightedBaseQReal T b :=
  qNorm_pos (baseQ T b)

/-- The actual theta value q_v^(j^2) for a signed label. -/
noncomputable def weightedThetaValueFromQ
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) : Real :=
  (weightedBaseQReal T b) ^ (gaussExponent j.1).toNat

/-- The actual signed representative theta log at a bad place and F_l^x label. -/
noncomputable def weightedThetaLocalLog
    (b : Bad (nativePlaceSelection T)) (j : ProcessionLabel l) : Real :=
  Real.log
    (weightedThetaValueFromQ T b
      (SignedLabel.representative l (j : ZMod l.value)))

/-- The actual F_l^x procession average of the signed theta logs at a bad
place.  The average is over F_l^x of cardinality l - 1. -/
noncomputable def weightedThetaLocalAverage
    (b : Bad (nativePlaceSelection T)) : Real :=
  processionAverage l (weightedThetaLocalLog (l := l) T b)

/-- The actual weighted Theta signed scalar: nativeBadLocalWeight-weighted sum
over the actual bad places of the F_l^x-averaged signed theta logs. -/
noncomputable def weightedThetaSignedScalar : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * weightedThetaLocalAverage (l := l) T b

/-- Exact local formula: the F_l^x average is the sum of the actual signed
theta logs divided by l - 1. -/
theorem weightedThetaLocalAverage_eq (b : Bad (nativePlaceSelection T)) :
    weightedThetaLocalAverage (l := l) T b =
      (∑ j : ProcessionLabel l, weightedThetaLocalLog (l := l) T b j) /
        (l.value - 1 : Real) := by
  unfold weightedThetaLocalAverage
  rw [processionAverage_formula]

/-- Actual weighted scalar formula with the F_l^x averaging denominator. -/
theorem weightedThetaSignedScalar_eq :
    weightedThetaSignedScalar (l := l) T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((∑ j : ProcessionLabel l, weightedThetaLocalLog (l := l) T b j) /
            (l.value - 1 : Real)) := by
  unfold weightedThetaSignedScalar
  apply Finset.sum_congr rfl
  intro b _
  rw [weightedThetaLocalAverage_eq]

/-- Direct signed comparison target: the weighted Theta signed scalar is at
least the native q-pilot normalized signed log-volume. -/
def WeightedThetaVsQPilotTarget : Prop :=
  weightedThetaSignedScalar (l := l) T >=
    nativeGlobalQPilotNormalizedSignedLogVolume T

/-- The target in its native q-pilot magnitude form. -/
theorem weightedThetaVsQPilotTarget_iff :
    WeightedThetaVsQPilotTarget (l := l) T ↔
      weightedThetaSignedScalar (l := l) T >=
        -nativeGlobalQPilotNormalizedLogMagnitude T := by
  unfold WeightedThetaVsQPilotTarget
    nativeGlobalQPilotNormalizedSignedLogVolume
  rfl


/-- The actual F_l^x weighted theta exponent coefficient as a natural sum over
the signed representatives of the unit labels. -/
def weightedThetaCoefficientNat (l : PrimeGeFive) : Nat :=
  ∑ j : ProcessionLabel l,
    (Int.natAbs
      (SignedLabel.representative l.value (j : ZMod l.value)).1) ^ 2

/-- The actual real F_l^x weighted theta coefficient. -/
noncomputable def weightedThetaCoefficient (l : PrimeGeFive) : Real :=
  ((l.value - 1 : Nat) : Real)⁻¹ * (weightedThetaCoefficientNat l : Real)

/-- The prime five as an actual PrimeGeFive. -/
def lFive : PrimeGeFive where
  value := 5
  prime := by norm_num
  ge_five := by norm_num

/-- Actual finite computation at l = 5: the unit representatives 1,2,3,4 have
squares 1,4,9,16, whose sum is 10. -/
theorem weightedThetaCoefficientNat_five :
    weightedThetaCoefficientNat lFive = 10 := by
  native_decide

/-- Actual l = 5 weighted theta coefficient: 10/(5-1) = 5/2. -/
theorem weightedThetaCoefficient_five :
    weightedThetaCoefficient lFive = 5 / 2 := by
  unfold weightedThetaCoefficient
  rw [weightedThetaCoefficientNat_five]
  norm_num

/-- Exact l = 5 scalar formula condition: the weighted Theta signed scalar is
- (5/2) times the q-pilot magnitude. -/
def WeightedThetaLFiveScalarFormula : Prop :=
  weightedThetaSignedScalar (l := lFive) T =
    -(5 / 2) * nativeGlobalQPilotNormalizedLogMagnitude T

/-- Exact l = 5 coefficient obstruction.  If the actual scalar formula holds
and the q-pilot magnitude is positive, the direct signed target is false:
- (5/2) Q < -Q. -/
theorem weightedThetaLFive_target_false
    (hformula : WeightedThetaLFiveScalarFormula (T := T))
    (hQ : 0 < nativeGlobalQPilotNormalizedLogMagnitude T) :
    ¬ WeightedThetaVsQPilotTarget (l := lFive) T := by
  intro htarget
  unfold WeightedThetaVsQPilotTarget at htarget
  unfold WeightedThetaLFiveScalarFormula at hformula
  unfold nativeGlobalQPilotNormalizedSignedLogVolume at htarget
  rw [hformula] at htarget
  linarith

end LeanFormal.IUT.XiFPaper.PaperWeightedThetaSignedActual

end
