/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1QPilotPlaceDegreeActual
import Mathlib.Tactic

/-!
# P6-B2: QCAND order/residue decomposition (single declaration cluster)

Status: CONDITIONAL/GAP.  Proves the exact equivalence of the pointwise QCAND
log equality with the product of candidate order and place residue-norm data,
using the two actual per-place formulas.  The order and residue equality are
kept as explicit named Props; no new structure fields, no sorry/axiom.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderResidueActual

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
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Pointwise QCAND: base-q log magnitude equals the native qVFamily absolute log. -/
def QCANDAt (b : Bad (nativePlaceSelection T)) : Prop :=
  baseQLogMagnitude T b = |Real.log (qVFamDefaultNorm T b)|

/-- Pointwise QCAND is exactly the order * residue-log equality. -/
theorem qcandAt_iff_order_residue (b : Bad (nativePlaceSelection T)) :
    QCANDAt T b ↔
      ((baseQ T b).order : Real) *
          Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
        qVFamTensorCoefficient T b *
          Real.log (residueNormBase (qVFamTensorPlace T b)) := by
  unfold QCANDAt
  rw [baseQLogMagnitude_eq_order_mul_log, nativeBadPlace_abs_log_eq]

/-- Order part of QCAND. -/
def QCANDOrderGap : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    (baseQ T b).order = (qVFamily T b).order

/-- Residue-norm part of QCAND. -/
def QCANDResNormGap : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    residueNormBase (nativeBaseSectionPlace T b) =
      residueNormBase (qVFamTensorPlace T b)

/-- Order + residue equality implies pointwise QCAND. -/
theorem qcandAt_of_order_resnorm
    (hord : QCANDOrderGap T) (hres : QCANDResNormGap T)
    (b : Bad (nativePlaceSelection T)) : QCANDAt T b := by
  have hord' : ∀ b : Bad (nativePlaceSelection T),
      (baseQ T b).order = (qVFamily T b).order := hord
  have hres' : ∀ b : Bad (nativePlaceSelection T),
      residueNormBase (nativeBaseSectionPlace T b) =
        residueNormBase (qVFamTensorPlace T b) := hres
  rw [qcandAt_iff_order_residue]
  rw [hord' b, hres' b]
  rfl

/-- Global QCAND from the two named subgaps. -/
theorem qcand_of_order_resnorm
    (hord : QCANDOrderGap T) (hres : QCANDResNormGap T) :
    ∀ b, QCANDAt T b :=
  fun b => qcandAt_of_order_resnorm T hord hres b

def qcandRows : List (String × String × String) :=
  [ ("qcandAt_iff_order_residue", "QCAND iff order*residue-log equality", "PROVED"),
    ("QCANDOrderGap", "baseQ order = qVFamily order", "GAP (Prop)"),
    ("QCANDResNormGap", "section K residue = native F residue", "GAP (Prop)"),
    ("qcand_of_order_resnorm", "ORDER+RESNORM => QCAND", "PROVED decomposition") ]

theorem qcandRows_length : qcandRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderResidueActual
