import tmp.sheaf.xif.paper.S371C3ScaledHullScalingClosedActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import tmp.sheaf.xif.paper.RootThetaValueInLUnitActual

/-!
# S384: normalized log object of the corrected C3 lattice hull

The corrected C3 unit region is the tensor lattice region from S349.  For
nonzero scalar a, the literal scaled hull is a*O (S353), it is base-Z_p-unit
scaling closed (S371), and its Haar is positive finite.  This file constructs

  normalizedMass = Haar(hull) / Haar(unit region),
  normalizedLog  = log Haar(hull) - log Haar(unit region),

with the hull/scaled-region formulas and the procession average over positive
Theta labels j.  Only log objects/formulas are built; no inequality is stated.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S384C3LatticeHullNormalizedLogActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.RootThetaValueInLUnitActual
open LeanFormal.IUT.XiFPaper.S349C3TensorLatticeRegionActual
open LeanFormal.IUT.XiFPaper.S353C3LatticeScaledHullActual
open LeanFormal.IUT.XiFPaper.S371C3ScaledHullScalingClosedActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Unit-region Haar mass. -/
noncomputable def c3LatticeUnitMass : ENNReal :=
  actualC3LogShellTensorHaar C3 (literalUnitRegion C3)

/-- Scaled-hull Haar mass. -/
noncomputable def c3LatticeHullMass (a : ℚ_[C3.p]) : ENNReal :=
  actualC3LogShellTensorHaar C3
    (literalHull C3 (literalScaledRegion C3 a))

/-- Normalized hull mass relative to the corrected unit region. -/
noncomputable def c3LatticeHullNormalizedMass
    (a : ℚ_[C3.p]) : ENNReal :=
  c3LatticeHullMass C3 a / c3LatticeUnitMass C3

/-- Unit mass is positive finite. -/
theorem c3LatticeUnitMass_pos_lt_top :
    0 < c3LatticeUnitMass C3 ∧ c3LatticeUnitMass C3 < ⊤ :=
  actualC3LogShellTensorLatticeRegion_measure_pos C3
    |> fun h => ⟨h, actualC3LogShellTensorLatticeRegion_measure_lt_top C3⟩

/-- Hull mass is positive finite for nonzero scalar. -/
theorem c3LatticeHullMass_pos_lt_top
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    0 < c3LatticeHullMass C3 a ∧ c3LatticeHullMass C3 a < ⊤ :=
  ⟨literalHull_measure_pos C3 a ha, literalHull_measure_lt_top C3 a ha⟩

/-- Normalized mass is positive. -/
theorem c3LatticeHullNormalizedMass_pos
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    0 < c3LatticeHullNormalizedMass C3 a := by
  unfold c3LatticeHullNormalizedMass
  exact ENNReal.div_pos
    (c3LatticeHullMass_pos_lt_top C3 a ha).1.ne'
    (c3LatticeUnitMass_pos_lt_top C3).2.ne

/-- Normalized mass is finite. -/
theorem c3LatticeHullNormalizedMass_lt_top
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    c3LatticeHullNormalizedMass C3 a < ⊤ := by
  unfold c3LatticeHullNormalizedMass
  exact ENNReal.div_lt_top
    (c3LatticeHullMass_pos_lt_top C3 a ha).2.ne
    (c3LatticeUnitMass_pos_lt_top C3).1.ne'

/-- Normalized hull log-volume. -/
noncomputable def c3LatticeHullNormalizedLog
    (a : ℚ_[C3.p]) : Real :=
  Real.log (c3LatticeHullMass C3 a).toReal -
    Real.log (c3LatticeUnitMass C3).toReal

/-- The normalized mass log equals the difference of the hull and unit logs. -/
theorem c3LatticeHullNormalizedMass_log_eq
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    Real.log (c3LatticeHullNormalizedMass C3 a).toReal =
      c3LatticeHullNormalizedLog C3 a := by
  unfold c3LatticeHullNormalizedMass c3LatticeHullNormalizedLog
  rw [ENNReal.toReal_div]
  have hh : (c3LatticeHullMass C3 a).toReal ≠ 0 := by
    simp [ENNReal.toReal_ne_zero,
      (c3LatticeHullMass_pos_lt_top C3 a ha).1.ne',
      (c3LatticeHullMass_pos_lt_top C3 a ha).2.ne]
  have hu : (c3LatticeUnitMass C3).toReal ≠ 0 := by
    simp [ENNReal.toReal_ne_zero,
      (c3LatticeUnitMass_pos_lt_top C3).1.ne',
      (c3LatticeUnitMass_pos_lt_top C3).2.ne]
  exact Real.log_div hh hu

/-- Region formula for the hull: nonzero a, hull = a*O. -/
theorem c3LatticeHull_eq_scaledRegion
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    literalHull C3 (literalScaledRegion C3 a) =
      literalScaledRegion C3 a :=
  literalHull_eq_scaledRegion C3 a ha

/-- Hull mass is the mass of a*O. -/
theorem c3LatticeHullMass_eq_scaledRegion
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    c3LatticeHullMass C3 a =
      actualC3LogShellTensorHaar C3 (literalScaledRegion C3 a) := by
  unfold c3LatticeHullMass
  rw [literalHull_eq_scaledRegion C3 a ha]

/-- Scaling/region package: nonzero-a hull is a*O, with positive finite Haar and
base-Z_p-unit scaling closedness. -/
structure C3LatticeHullNormalizedLogObject
    (a : ℚ_[C3.p]) (ha : a ≠ 0) where
  unitRegion : Set (C3LogShellTensorBlock C3)
  unitRegion_eq : unitRegion = literalUnitRegion C3
  hull : Set (C3LogShellTensorBlock C3)
  hull_eq : hull = literalHull C3 (literalScaledRegion C3 a)
  hull_eq_scaledRegion : hull = literalScaledRegion C3 a
  unitMass : ENNReal
  unitMass_eq : unitMass = c3LatticeUnitMass C3
  unitMass_pos_lt_top : 0 < unitMass ∧ unitMass < ⊤
  hullMass : ENNReal
  hullMass_eq : hullMass = c3LatticeHullMass C3 a
  hullMass_pos_lt_top : 0 < hullMass ∧ hullMass < ⊤
  normalizedMass : ENNReal
  normalizedMass_eq : normalizedMass = c3LatticeHullNormalizedMass C3 a
  normalizedMass_pos : 0 < normalizedMass
  normalizedMass_lt_top : normalizedMass < ⊤
  normalizedLog : Real
  normalizedLog_eq : normalizedLog = c3LatticeHullNormalizedLog C3 a
  scaling_closed : BaseZPUnitScalingClosed C3 hull

/-- Actual normalized-log object constructor. -/
noncomputable def c3LatticeHullNormalizedLogObject
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    C3LatticeHullNormalizedLogObject C3 a ha where
  unitRegion := literalUnitRegion C3
  unitRegion_eq := rfl
  hull := literalHull C3 (literalScaledRegion C3 a)
  hull_eq := rfl
  hull_eq_scaledRegion := literalHull_eq_scaledRegion C3 a ha
  unitMass := c3LatticeUnitMass C3
  unitMass_eq := rfl
  unitMass_pos_lt_top := c3LatticeUnitMass_pos_lt_top C3
  hullMass := c3LatticeHullMass C3 a
  hullMass_eq := rfl
  hullMass_pos_lt_top := c3LatticeHullMass_pos_lt_top C3 a ha
  normalizedMass := c3LatticeHullNormalizedMass C3 a
  normalizedMass_eq := rfl
  normalizedMass_pos := c3LatticeHullNormalizedMass_pos C3 a ha
  normalizedMass_lt_top := c3LatticeHullNormalizedMass_lt_top C3 a ha
  normalizedLog := c3LatticeHullNormalizedLog C3 a
  normalizedLog_eq := rfl
  scaling_closed := literalHull_scalingClosed C3 a ha

/-- Procession average over positive Theta labels. -/
noncomputable def c3LatticeHullProcessionAverageLog
    (a : ℚ_[C3.p]) (ha : a ≠ 0) : Real :=
  ∑ j : ThetaLabel (l := l),
    (Fintype.card (ThetaLabel (l := l)) : Real)⁻¹ *
      c3LatticeHullNormalizedLog C3 a

/-- The procession average is the normalized hull log (label-independent hull). -/
theorem c3LatticeHullProcessionAverageLog_eq
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    c3LatticeHullProcessionAverageLog C3 a ha =
      c3LatticeHullNormalizedLog C3 a := by
  unfold c3LatticeHullProcessionAverageLog
  haveI : Nonempty (ThetaLabel (l := l)) := thetaLabel_nonempty (l := l)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (ThetaLabel (l := l)) : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hcard]

end LeanFormal.IUT.XiFPaper.S384C3LatticeHullNormalizedLogActual

end
