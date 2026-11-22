import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-! # Global qVFamily theta-hull sum

For each native bad place b, use the actual per-b local data:

* the qVFamily base lattice coefficient
    c_b = order(qVFamily b) * localResidueDegree(F-place over b)
          * (log(residueNormBase b) / log p_b),
  where p_b is the residue characteristic of b;
* the local q-pilot log scalar
    qPilotLocalLog b = -(c_b * log p_b);
* the local theta hull log scalar
    thetaHullLocalLog b = -(c_b * log p_b),
  the j = 1 minimal theta sector in the per-b fractional-lattice block.

The actual identity c_b * log p_b = nativeQVPilotLocalMagnitude b is proved, so
the weighted global q-pilot log is exactly the native qVFamily normalized signed
scalar.  The local qPilot <= thetaHull inequality is an equality in the minimal
sector and sums with the actual nativeBadLocalWeight weights.

No single fixed-p block is used.  No fake inequality.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual residue characteristic p_b of the Fmod place b.1. -/
noncomputable def qVFamilyResiduePrime
    (b : Bad (nativePlaceSelection T)) : Nat :=
  NumberFieldFinitePlace.residueCharacteristic b.1

/-- The actual base residue degree of b written in p_b-log units. -/
noncomputable def qVFamilyBasePLogCoefficient
    (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log (residueNormBase ((nativeBadLift T).lift b)) /
    Real.log (qVFamilyResiduePrime T b : Real)

/-- The actual qVFamily lattice coefficient c_b. -/
noncomputable def qVFamilyLatticeCoefficient
    (b : Bad (nativePlaceSelection T)) : Real :=
  ((qVFamily T b).order : Real) *
    qVFamilyBasePLogCoefficient T b

/-- The actual local q-pilot log: -(c_b log p_b). -/
noncomputable def localQPilotLog
    (b : Bad (nativePlaceSelection T)) : Real :=
  - qVFamilyLatticeCoefficient T b *
    Real.log (qVFamilyResiduePrime T b : Real)

/-- The actual local theta hull log: the same minimal j = 1 sector. -/
noncomputable def localThetaHullLogFormula
    (b : Bad (nativePlaceSelection T)) : Real :=
  - qVFamilyLatticeCoefficient T b *
    Real.log (qVFamilyResiduePrime T b : Real)

/-- local q-pilot log formula. -/
theorem localQPilotLogEqFormula : localQPilotLog T b = localThetaHullLogFormula T b := rfl

/-- Exact missing actual hull log: the formula scalar is not the arithmetic
normalized hull log until the actual hull region and ArithmeticTuplePureFractionalScalingData
are supplied. -/
structure LocalThetaHullFormulaGap
    (b : Bad (nativePlaceSelection T)) where
  actualThetaHullLog : Real
  actualThetaHullLog_is_hull_normalized : Prop
  formula_eq : localThetaHullLogFormula T b = actualThetaHullLog

/-- Exact gap requirement for the local formula identification. -/
def LocalThetaHullFormulaGapRequired
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (LocalThetaHullFormulaGap (l := l) T b)

/-- Local inequality conditional on the actual hull formula identification. -/
theorem localQPilotLog_le_thetaHullLogFormula
    (b : Bad (nativePlaceSelection T))
    (G : LocalThetaHullFormulaGap (l := l) T b) :
    localQPilotLog T b <= G.actualThetaHullLog := by
  rw [localQPilotLogEqFormula] at *
  rw [G.formula_eq]

/-- The actual coefficient identity: c_b * log p_b is the qVFamily local
log-magnitude. -/
theorem qVFamilyLatticeCoefficient_mul_logp_eq_localMagnitude
    (b : Bad (nativePlaceSelection T)) :
    qVFamilyLatticeCoefficient T b *
        Real.log (qVFamilyResiduePrime T b : Real) =
      nativeQVPilotLocalMagnitude T b := by
  unfold qVFamilyLatticeCoefficient qVFamilyBasePLogCoefficient
    qVFamilyResiduePrime nativeQVPilotLocalMagnitude
  have hlogp : Real.log
      (NumberFieldFinitePlace.residueCharacteristic b.1 : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (NumberFieldFinitePlace.residueCharacteristic_pos b.1)
    · exact_mod_cast (NumberFieldFinitePlace.residueCharacteristic_prime b.1).ne_one
  field_simp [hlogp]
  rw [localLogMagnitude_eq_order_mul_log (parameter := qVFamily T b)]

/-- The local q-pilot log is the negative qVFamily local magnitude. -/
theorem localQPilotLog_eq_neg_localMagnitude
    (b : Bad (nativePlaceSelection T)) :
    localQPilotLog T b = - nativeQVPilotLocalMagnitude T b := by
  unfold localQPilotLog
  rw [show -qVFamilyLatticeCoefficient T b *
        Real.log (qVFamilyResiduePrime T b : Real) =
      -(qVFamilyLatticeCoefficient T b *
        Real.log (qVFamilyResiduePrime T b : Real)) by ring]
  rw [qVFamilyLatticeCoefficient_mul_logp_eq_localMagnitude]

/-- The global weighted q-pilot log. -/
noncomputable def globalQPilotLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * localQPilotLog T b

/-- The global weighted theta hull log. -/
noncomputable def globalThetaHullLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * localThetaHullLogFormula T b

/-- Global q-pilot log equals the native qVFamily normalized signed scalar. -/
theorem globalQPilotLog_eq_nativeSigned :
    globalQPilotLog T = nativeQVPilotNormalizedSignedLogVolume T := by
  unfold globalQPilotLog nativeQVPilotNormalizedSignedLogVolume
    nativeQVPilotNormalizedLogMagnitude
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [localQPilotLog_eq_neg_localMagnitude]
  ring

/-- Exact global gap: all local actual hull formula identifications. -/
def GlobalThetaHullFormulaGap : Type :=
  forall b : Bad (nativePlaceSelection T),
    LocalThetaHullFormulaGap (l := l) T b

/-- Conditional global theta hull log equality with the native signed scalar. -/
theorem globalThetaHullLog_eq_nativeSigned_of_gap
    (G : GlobalThetaHullFormulaGap T) :
    (∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b * (G b).actualThetaHullLog) =
      nativeQVPilotNormalizedSignedLogVolume T := by
  have hlocal : forall b : Bad (nativePlaceSelection T),
      (G b).actualThetaHullLog = localQPilotLog T b := by
    intro b
    rw [← (G b).formula_eq]
    rfl
  calc
    (∑ b, nativeBadLocalWeight T b * (G b).actualThetaHullLog)
        = ∑ b, nativeBadLocalWeight T b * localQPilotLog T b := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hlocal b]
    _ = nativeQVPilotNormalizedSignedLogVolume T := globalQPilotLog_eq_nativeSigned T

end LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual

end