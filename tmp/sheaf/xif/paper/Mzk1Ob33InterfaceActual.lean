/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1WeightedDetPacketActual
import tmp.sheaf.xif.paper.S3134ThetaHullDetNormalizationActual
import Mathlib.Tactic

/-! # P7 / (Ob3-3) partial interface: det(x)M source identification ⇒ packet/degree chain -/

/-
| field | value |
|---|---|
| Status | PARTIAL INTERFACE (non-discharge): named source identification hypothesis connects the S3134 det-normalization law to the WeightedDetPacket C17 chain |
| Reuse | `Mzk1WeightedDetPacketActual:42/56/63`（GAP_P6_C17_DICT, weighted diff = N*M）; `S3134ThetaHullDetNormalizationActual:65/77`（det normalization law; green, but its `detData` fields are the remaining source data） |
| GAP | GAP-P7-OB33-SRC: the actual source identification `det(x)M output arithmetic degree = normalized log-volume` is a named input here, NOT constructed; #3 remains partial |
| 纪律 | no sorry/axiom; the source identification is an explicit named hypothesis, not a structure field used to fake proof |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33InterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketActual

/-- **(Ob3-3) named source identification**: the det(x)M-normalized Theta-side
reading equals the packet's actual theta reading.  This is the missing source
identification, kept as an explicit hypothesis. -/
def Ob33SourceIdentification (detTheta thetaActual : Real) : Prop :=
  detTheta = thetaActual

theorem Ob33SourceIdentification_iff (detTheta thetaActual : Real) :
    Ob33SourceIdentification detTheta thetaActual ↔ detTheta = thetaActual :=
  Iff.rfl

/-- **Conditional (Ob3-3) interface**: under the named source identification, the
weighted packet difference is `N * (detTheta - qActual)`, i.e. the det-normalized
Theta reading enters the C17 weighted identity in place of the raw theta reading. -/
theorem ob33_interface_weighted_eq
    {label : Type*} [Fintype label]
    (P Q : WeightedDeterminantPacket label)
    (hden : P.denominator = Q.denominator)
    (qActual thetaActual detTheta : Real)
    (hgap : GAP_P6_C17_DICT P.normalizedLogVolume Q.normalizedLogVolume
      qActual thetaActual)
    (hsrc : Ob33SourceIdentification detTheta thetaActual) :
    Q.weightedLogVolume - P.weightedLogVolume =
      (P.commonTensorDegree : Real) * (detTheta - qActual) := by
  rw [← hsrc] at hgap
  exact weightedLogVolume_sub_eq_commonTensorDegree_mul_M P Q hden
    (detTheta - qActual) qActual detTheta hgap rfl

/-- **Non-vacuity guard**: the named identification is reflexive for the actual
reading (this is the only unconditional instance; it does not identify det(x)M). -/
theorem ob33_interface_weighted_eq_self
    {label : Type*} [Fintype label]
    (P Q : WeightedDeterminantPacket label)
    (hden : P.denominator = Q.denominator)
    (qActual thetaActual : Real)
    (hgap : GAP_P6_C17_DICT P.normalizedLogVolume Q.normalizedLogVolume
      qActual thetaActual) :
    Q.weightedLogVolume - P.weightedLogVolume =
      (P.commonTensorDegree : Real) * (thetaActual - qActual) :=
  ob33_interface_weighted_eq P Q hden qActual thetaActual thetaActual hgap rfl

def ob33Rows : List (String × String) :=
  [ ("Ob33SourceIdentification", "named source identification detTheta = thetaActual (explicit hypothesis)") ,
    ("ob33_interface_weighted_eq", "conditional: weighted diff = N*(detTheta - qActual)") ,
    ("ob33_interface_weighted_eq_self", "unconditional instance (thetaActual itself)") ,
    ("GAP-P7-OB33-SRC", "actual det(x)M arithmetic degree = normalized log-volume NOT constructed") ,
    ("S3134 det law", "S3134ThetaHullDetLogVolume_eq_of_gap: det-normalized hull = tensorPowerExponent * hull") ]

theorem ob33Rows_length : ob33Rows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33InterfaceActual