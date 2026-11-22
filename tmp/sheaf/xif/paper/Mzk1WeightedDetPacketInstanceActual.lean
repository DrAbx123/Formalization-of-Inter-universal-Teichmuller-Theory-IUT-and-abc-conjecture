/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.WeightedNormalization
import tmp.sheaf.xif.paper.Mzk1WeightedDetPacketActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4FKDescentBridge
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Mzk1QPilotPlaceDegreeActual
import tmp.sheaf.xif.paper.Mzk1DegreeSumActual
import Mathlib.Tactic

/-!
# P6-B1: concrete WeightedDeterminantPacket instance from actual q/Theta coefficients

Status: PARTIAL/green-target candidate.

This file constructs two concrete `WeightedDeterminantPacket` instances on the actual
native bad index:

* `qPacket`: hull log-degree is the actual signed q log `-baseQLogMagnitude`,
  denominator is the paper root denominator `2*l`;
* `thetaPacket`: hull log-degree is the actual classical Theta coefficient
  `-sum_j j^2*order(q_b)*log(p_b)`, same denominator `2*l`.

Both therefore have common tensor degree `(2*l)^#Bad`. The normalized readings are
reduced to concrete actual sums. The identification of these sums with the
DegreeBridge/DegreeSum and paper-root-Theta readings is the named gap
`GAP_P6_C17_DICT_INST`; it is never a structure field or an assumed theorem.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotPlaceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1DegreeSumActual
open LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- QPLACE, comap form (PROVED): the section lift and the lying-over lift have
the same contraction.  This is exactly `sectionFiniteLift_comap` plus
`nativeBadLift.lift_comap`; it does NOT identify the two Classical choices. -/
theorem qplace_comap_eq (b : Bad (nativePlaceSelection T)) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        (sectionFiniteLift (nativePlaceSelection T) b.1) =
      NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        ((nativeBadLift T).lift b) := by
  rw [sectionFiniteLift_comap, (nativeBadLift T).lift_comap]

/-- QPLACE: the section lift and the lying-over lift are the same F-place.
This is NOT provable from the two comap equalities: both sides are different
`Classical.choose` values (`SourcePlacePartitionReduction:322` vs
`NativeBadLiftActual:22`).  Kept as a named gap. -/
def GAP_P6_C17_QPLACE (b : Bad (nativePlaceSelection T)) : Prop :=
  fkDescentShadow (nativePlaceSelection T) b.1 = (nativeBadLift T).lift b

/-- QCAND: the base-q candidate and the qVFamily candidate have the same local
log magnitude at each bad place.  This is the pointwise candidate/order data on
top of QPLACE; kept as a named gap, not a structure field. -/
def GAP_P6_C17_QCAND : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    baseQLogMagnitude T b = |Real.log (qVFamDefaultNorm T b)|

/-- Named q-side bridge: the actual base-q total log magnitude equals the native
qVFamily absolute-log sum used by DegreeSum.  This is NOT definitional:
`baseQ = nativeBaseQFamily` (BaseQFamilyActual:59) is independent of
`qVFamily` (BaseQFamilyActual:20-22), and `nativeBadQAbsLogSum` uses
`qVFamDefaultNorm = ‖(qVFamily T b).q‖` (QVFamNormalizedCoefficientBridgeActual:59). -/
def GAP_P6_C17_QHALF : Prop :=
  baseQTotalLogMagnitude T = nativeBadQAbsLogSum T

/-- Exact order/residue decomposition of QCAND, using the two actual per-place
formulas: `baseQLogMagnitude = order(baseQ)*log(residue section K-place)` and
`|log qVFamDefaultNorm| = qVFam order * log(residue native F-place)`. -/
theorem qcand_iff_order_residue (b : Bad (nativePlaceSelection T)) :
    baseQLogMagnitude T b = |Real.log (qVFamDefaultNorm T b)| ↔
      ((baseQ T b).order : Real) *
          Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
        qVFamTensorCoefficient T b *
          Real.log (residueNormBase (qVFamTensorPlace T b)) := by
  rw [baseQLogMagnitude_eq_order_mul_log, nativeBadPlace_abs_log_eq]

/-- Order part of QCAND: base-q candidate order equals qVFamily order. -/
def GAP_P6_C17_QCAND_ORDER : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    (baseQ T b).order = (qVFamily T b).order

/-- Residue-norm part of QCAND: the section K-place and the native F-place have
the same residue-norm base. -/
def GAP_P6_C17_QCAND_RESNORM : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    residueNormBase (nativeBaseSectionPlace T b) =
      residueNormBase (qVFamTensorPlace T b)

/-- QCAND follows from the two explicit order/residue subgaps. -/
theorem QCAND_of_order_resnorm
    (hord : GAP_P6_C17_QCAND_ORDER T)
    (hres : GAP_P6_C17_QCAND_RESNORM T) :
    GAP_P6_C17_QCAND T := by
  intro b
  have hord' : ∀ b : Bad (nativePlaceSelection T),
      (baseQ T b).order = (qVFamily T b).order := hord
  have hres' : ∀ b : Bad (nativePlaceSelection T),
      residueNormBase (nativeBaseSectionPlace T b) =
        residueNormBase (qVFamTensorPlace T b) := hres
  rw [qcand_iff_order_residue]
  rw [hord' b, hres' b]
  rfl

/-- Decomposition: QPLACE + QCAND imply QHALF.  The q-side total is reduced to
the pointwise candidate log equality. -/
theorem QHALF_of_QPLACE_QCAND
    (_hplace : ∀ b : Bad (nativePlaceSelection T), GAP_P6_C17_QPLACE T b)
    (hcand : GAP_P6_C17_QCAND T) :
    GAP_P6_C17_QHALF T := by
  unfold GAP_P6_C17_QHALF baseQTotalLogMagnitude nativeBadQAbsLogSum
  apply Finset.sum_congr rfl
  intro b _
  exact hcand b

/-- The paper root denominator `2*l`, as a positive natural. -/
def paperRootDenominator : ℕ+ :=
  show ℕ+ from
    (⟨2 * l.value, Nat.mul_pos (by norm_num) l.prime.pos⟩ : { n : ℕ // 0 < n })

theorem paperRootDenominator_natCast :
    (paperRootDenominator (l := l) : ℕ) = 2 * l.value := by
  unfold paperRootDenominator
  rfl

theorem paperRootDenominator_cast :
    ((paperRootDenominator (l := l) : ℕ) : ℝ) = 2 * (l.value : ℝ) := by
  rw [paperRootDenominator_natCast]
  norm_num

/-- Concrete q-side packet: actual signed q log-degree, denominator `2*l`. -/
noncomputable def qPacket : WeightedDeterminantPacket (Bad (nativePlaceSelection T)) where
  hullLogDegree b := -baseQLogMagnitude T b
  structureSheafLogDegree := 0
  denominator _ := paperRootDenominator (l := l)

/-- Concrete Theta-side packet: actual classical coefficient
`-sum_j j^2*order(q_b)*log(p_b)`, denominator `2*l`. -/
noncomputable def thetaHullLogDegree (b : Bad (nativePlaceSelection T)) : Real :=
  -∑ j : SignedLabel l.value,
    qVFamThetaTensorCoefficient T b j () * Real.log (qVFamTensorP T b : Real)

noncomputable def thetaPacket : WeightedDeterminantPacket (Bad (nativePlaceSelection T)) where
  hullLogDegree b := thetaHullLogDegree T b
  structureSheafLogDegree := 0
  denominator _ := paperRootDenominator (l := l)

/-- The q packet's common tensor degree is the actual clearing constant. -/
theorem qPacket_commonTensorDegree :
    (qPacket (l := l) T).commonTensorDegree =
      (2 * l.value) ^ Fintype.card (Bad (nativePlaceSelection T)) := by
  unfold WeightedDeterminantPacket.commonTensorDegree
  have h : ∀ i, ((qPacket (l := l) T).denominator i : ℕ) = 2 * l.value := by
    intro i
    simp [qPacket, paperRootDenominator_natCast]
  calc
    (∏ i, ((qPacket (l := l) T).denominator i : ℕ)) = ∏ _i, 2 * l.value := by
      apply Finset.prod_congr rfl
      intro i _
      exact h i
    _ = (2 * l.value) ^ Fintype.card (Bad (nativePlaceSelection T)) := by
      rw [Finset.prod_const]
      simp

/-- The Theta packet's common tensor degree is the same actual clearing constant. -/
theorem thetaPacket_commonTensorDegree :
    (thetaPacket (l := l) T).commonTensorDegree =
      (2 * l.value) ^ Fintype.card (Bad (nativePlaceSelection T)) := by
  unfold WeightedDeterminantPacket.commonTensorDegree
  have h : ∀ i, ((thetaPacket (l := l) T).denominator i : ℕ) = 2 * l.value := by
    intro i
    simp [thetaPacket, paperRootDenominator_natCast]
  calc
    (∏ i, ((thetaPacket (l := l) T).denominator i : ℕ)) = ∏ _i, 2 * l.value := by
      apply Finset.prod_congr rfl
      intro i _
      exact h i
    _ = (2 * l.value) ^ Fintype.card (Bad (nativePlaceSelection T)) := by
      rw [Finset.prod_const]
      simp

/-- The q packet's normalized reading is the actual q signed sum divided by `2*l`. -/
theorem qPacket_normalizedLogVolume :
    (qPacket (l := l) T).normalizedLogVolume =
      -(∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b) /
        (2 * l.value : Real) := by
  unfold WeightedDeterminantPacket.normalizedLogVolume
    WeightedDeterminantPacket.adjustedLogDegree qPacket
  simp only [sub_zero]
  rw [← Finset.sum_div]
  rw [paperRootDenominator_cast]
  congr 1
  rw [Finset.sum_neg_distrib]

/-- The Theta packet's normalized reading is the actual classical Theta sum divided by `2*l`. -/
theorem thetaPacket_normalizedLogVolume :
    (thetaPacket (l := l) T).normalizedLogVolume =
      (∑ b : Bad (nativePlaceSelection T), thetaHullLogDegree T b) /
        (2 * l.value : Real) := by
  unfold WeightedDeterminantPacket.normalizedLogVolume
    WeightedDeterminantPacket.adjustedLogDegree thetaPacket
  simp only [sub_zero]
  rw [← Finset.sum_div]
  rw [paperRootDenominator_cast]

/-- The q packet normalized reading against the actual base-q total log magnitude. -/
noncomputable def qActualBaseNormalized : Real :=
  -baseQTotalLogMagnitude T / (2 * l.value : Real)

/-- **q half, base-q form (PROVED)**: the q packet normalized reading is exactly
the actual base-q total log magnitude divided by `2*l`. -/
theorem qPacket_normalized_eq_qActualBase :
    (qPacket (l := l) T).normalizedLogVolume = qActualBaseNormalized (l := l) T := by
  unfold qActualBaseNormalized
  rw [qPacket_normalizedLogVolume, baseQTotalLogMagnitude_eq_sum]

/-- Actual q reading using the DegreeSum/degree bridge weight `nativeBadQAbsLogSum`. -/
noncomputable def qActualNormalized : Real :=
  -nativeBadQAbsLogSum T / (2 * l.value : Real)

/-- q half in the original `nativeBadQAbsLogSum` form, conditional on the exact
QBase↔qVFamily bridge (`GAP-P6-C17-QHALF`). -/
theorem qPacket_normalized_eq_qActualNormalized_of_qhalf
    (h : GAP_P6_C17_QHALF T) :
    (qPacket (l := l) T).normalizedLogVolume = qActualNormalized (l := l) T := by
  rw [qPacket_normalized_eq_qActualBase]
  unfold qActualBaseNormalized qActualNormalized
  rw [h]

/-- q-half in native form, with QPLACE and QCAND as the two explicit named
inputs (instead of the single QHALF hypothesis). -/
theorem qPacket_normalized_eq_qActualNormalized_of_qplace_qcand
    (hplace : ∀ b : Bad (nativePlaceSelection T), GAP_P6_C17_QPLACE T b)
    (hcand : GAP_P6_C17_QCAND T) :
    (qPacket (l := l) T).normalizedLogVolume = qActualNormalized (l := l) T :=
  qPacket_normalized_eq_qActualNormalized_of_qhalf (T := T)
    (QHALF_of_QPLACE_QCAND T hplace hcand)


/-- Actual Theta reading using the concrete classical coefficient sum (candidate; the
paper-root-hull equality is the gap). -/
noncomputable def thetaActualNormalized : Real :=
  (∑ b : Bad (nativePlaceSelection T), thetaHullLogDegree T b) /
    (2 * l.value : Real)

/-- Named exact gap for the concrete instance: the packet normalized readings are the
actual q/Theta readings.  This is a `Prop`, not a structure field. -/
def GAP_P6_C17_DICT_INST : Prop :=
  (qPacket (l := l) T).normalizedLogVolume = qActualNormalized (l := l) T ∧
    (thetaPacket (l := l) T).normalizedLogVolume = thetaActualNormalized (l := l) T

/-- Conditional concrete (C17): under the named instance gap and `thetaActual-qActual=M`,
the concrete packet weighted difference is `N*M` with the actual clearing constant. -/
theorem c17_instance_weightedDiff_eq_mul_M
    (M : Real)
    (hgap : GAP_P6_C17_DICT_INST (l := l) T)
    (hM : thetaActualNormalized (l := l) T - qActualNormalized (l := l) T = M) :
    (thetaPacket (l := l) T).weightedLogVolume -
        (qPacket (l := l) T).weightedLogVolume =
      ((2 * l.value) ^ Fintype.card (Bad (nativePlaceSelection T)) : Real) * M := by
  have hden : (thetaPacket (l := l) T).denominator =
      (qPacket (l := l) T).denominator := rfl
  have h := weightedLogVolume_sub_eq_commonTensorDegree_mul_normalized_sub
    (thetaPacket (l := l) T) (qPacket (l := l) T) hden
  rw [h, hgap.1, hgap.2, hM]
  rw [commonTensorDegree_eq_of_denominator_eq
    (thetaPacket (l := l) T) (qPacket (l := l) T) hden]
  rw [qPacket_commonTensorDegree]
  norm_num

def p6bRows : List (String × String × String) :=
  [ ("qPacket", "actual signed q log, denominator 2l", "DEF (concrete)"),
    ("thetaPacket", "actual classical Theta coefficient sum, denominator 2l", "DEF (concrete)"),
    ("qPacket_commonTensorDegree", "(2l)^#Bad", "PROVED"),
    ("thetaPacket_commonTensorDegree", "(2l)^#Bad", "PROVED"),
    ("qPacket_normalizedLogVolume", "actual q normalized sum", "PROVED"),
    ("thetaPacket_normalizedLogVolume", "actual Theta normalized sum", "PROVED"),
    ("qPacket_normalized_eq_qActualBase", "q packet = actual base-q total/(2l)", "PROVED"),
    ("GAP_P6_C17_QPLACE", "sectionFiniteLift = nativeBadLift.lift (choice gap)", "GAP (Prop, precise)"),
    ("qcand_iff_order_residue", "QCAND iff order*log(residue) equality", "PROVED"),
    ("GAP_P6_C17_QCAND_ORDER", "baseQ.order = qVFamily.order", "GAP (Prop)"),
    ("GAP_P6_C17_QCAND_RESNORM", "residue(sectionKPlace)=residue(nativeFPlace)", "GAP (Prop)"),
    ("QCAND_of_order_resnorm", "ORDER+RESNORM => QCAND", "PROVED decomposition"),
    ("GAP_P6_C17_QCAND", "baseQ log = |log qVFamDefaultNorm| per b", "GAP (Prop, precise)"),
    ("QHALF_of_QPLACE_QCAND", "QPLACE+QCAND => QHALF", "PROVED decomposition"),
    ("GAP_P6_C17_QHALF", "baseQ total = nativeBadQAbsLogSum (QBase vs qVFamily)", "GAP (Prop, precise)"),
    ("qPacket_normalized_eq_qActualNormalized_of_qhalf", "q half native form conditional on QHALF", "PROVED conditional"),
    ("qPacket_normalized_eq_qActualNormalized_of_qplace_qcand", "q half with QPLACE+QCAND explicit", "PROVED conditional"),
    ("GAP_P6_C17_DICT_INST", "packet normalized = actual DegreeBridge/paper Theta readings", "GAP (Prop)"),
    ("c17_instance_weightedDiff_eq_mul_M", "weighted difference = N*M conditional on gap", "PROVED conditional") ]

theorem p6bRows_length : p6bRows.length = 19 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketInstanceActual
