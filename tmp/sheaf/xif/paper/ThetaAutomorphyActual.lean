import LeanFormal.IUT.Foundations.Theta.OddThetaShift
import LeanFormal.IUT.Foundations.Theta.OddTheta
import LeanFormal.IUT.Foundations.Theta.OddThetaNormalization

/-!
# Actual theta automorphy factor and lattice action

Source: EtTh Proposition 1.4, (ii), as used in IUT II, Introduction p.2-3 and
Remark 2.5.1, p.72-73. For the odd theta series with q and a chosen square root
r (r^2 = q, r != 0), the actual shift law is

  oddTheta q (r^a * U) =
    oddThetaSign a * r^(-(a^2)) * U^(-(2a)) * oddTheta q U

for a in Z. This file constructs the actual automorphy factor

  thetaAutomorphyFactor D a U := oddThetaSign a * r^(-(a^2)) * U^(-(2a)),

the actual lattice/period action U |-> r^a * U, and proves the shift law.

The factor is L-valued, matching the actual odd theta series carrier. The
quotient trivial line bundle by this automorphy action and its comparison with
the source curve theta line bundle are not constructed here; no product,
quotient type, or source curve identification is fabricated.

No inequality is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ABCBridge.ThetaAutomorphyActual

open LeanFormal.IUT.Foundations.Theta

universe u

/-- Actual theta period/root data: q, a chosen square root r, and the
ultrametric convergence condition. -/
structure ThetaPeriodData (L : Type u) [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L] where
  q : L
  r : L
  r_sq : r ^ 2 = q
  r_ne_zero : r ≠ 0
  q_norm_lt_one : ‖q‖ < 1

/-- The actual automorphy factor of the odd theta shift law. -/
def thetaAutomorphyFactor {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (a : ℤ) (U : L) : L :=
  oddThetaSign a * D.r ^ (-(a ^ 2)) * U ^ (-(2 * a))

/-- The actual lattice/period action on the multiplicative coordinate. -/
def thetaLatticeAction {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (a : ℤ) (U : L) : L :=
  D.r ^ a * U

/-- The actual theta shift law expressed with the constructed factor and lattice
action. -/
theorem thetaAutomorphy_shift {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : L) (hU : U ≠ 0) (a : ℤ) :
    oddTheta D.q (thetaLatticeAction D a U) =
      thetaAutomorphyFactor D a U * oddTheta D.q U := by
  simpa [thetaLatticeAction, thetaAutomorphyFactor]
    using oddTheta_shift D.q D.r U D.r_sq D.r_ne_zero hU
      D.q_norm_lt_one a

/-- The lattice action at zero is the identity. -/
theorem thetaLatticeAction_zero {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : L) :
    thetaLatticeAction D 0 U = U := by
  simp [thetaLatticeAction]

/-- The actual automorphy factor at zero is one. -/
theorem thetaAutomorphyFactor_zero {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : L) :
    thetaAutomorphyFactor D 0 U = 1 := by
  simp [thetaAutomorphyFactor]

/-- The actual theta section transformed by the automorphy factor. -/
def thetaAutomorphySection {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : L) : L :=
  oddTheta D.q U

/-- The transformed section is exactly the factor times the original section. -/
theorem thetaAutomorphySection_shift
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : L) (hU : U ≠ 0) (a : ℤ) :
    thetaAutomorphySection D (thetaLatticeAction D a U) =
      thetaAutomorphyFactor D a U * thetaAutomorphySection D U :=
  thetaAutomorphy_shift D U hU a

/-- The standard unit -1, used for the theta sign factor. -/
def oddThetaSignUnit {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L] (a : ℤ) : Lˣ :=
  Units.mk0 (oddThetaSign a) (by
    rw [oddThetaSign_eq_pow]
    exact zpow_ne_zero _ (by norm_num : (-1 : L) ≠ 0))

/-- The chosen square root r as a unit. -/
def thetaRootUnit {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L] (D : ThetaPeriodData L) : Lˣ :=
  Units.mk0 D.r D.r_ne_zero

/-- The actual automorphy factor as a unit. -/
def thetaAutomorphyUnit {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (a : ℤ) (U : Lˣ) : Lˣ :=
  oddThetaSignUnit a * (thetaRootUnit D) ^ (-(a ^ 2)) * U ^ (-(2 * a))

/-- The lattice action on units. -/
def thetaUnitAction {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (a : ℤ) (U : Lˣ) : Lˣ :=
  (thetaRootUnit D) ^ a * U

/-- The sign units are multiplicative. -/
theorem oddThetaSignUnit_add {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L] (a b : ℤ) :
    oddThetaSignUnit (L := L) (a + b) =
      oddThetaSignUnit (L := L) a * oddThetaSignUnit (L := L) b := by
  ext
  simp [oddThetaSignUnit, oddThetaSign_add]

/-- The actual factor cocycle in the unit group. -/
theorem thetaAutomorphyUnit_cocycle {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (a b : ℤ) (U : Lˣ) :
    thetaAutomorphyUnit D (a + b) U =
      thetaAutomorphyUnit D a (thetaUnitAction D b U) *
        thetaAutomorphyUnit D b U := by
  unfold thetaAutomorphyUnit thetaUnitAction
  rw [oddThetaSignUnit_add]
  group

/-- The actual L-valued factor cocycle. -/
theorem thetaAutomorphyFactor_cocycle {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : L) (hU : U ≠ 0) (a b : ℤ) :
    thetaAutomorphyFactor D (a + b) U =
      thetaAutomorphyFactor D a (thetaLatticeAction D b U) *
        thetaAutomorphyFactor D b U := by
  have h := congrArg (fun z : Lˣ => (z : L))
    (thetaAutomorphyUnit_cocycle D a b (Units.mk0 U hU))
  simpa [thetaAutomorphyUnit, thetaAutomorphyFactor, thetaUnitAction,
    thetaLatticeAction, thetaRootUnit, Units.val_mul, Units.val_pow_eq_pow_val] using h

/-- Actual inhabitant of the factor-cocycle structure. -/
structure ThetaAutomorphyCocycle
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : Prop where
  cocycle_relation : ∀ (a b : ℤ) (U : L), U ≠ 0 →
    thetaAutomorphyFactor D (a + b) U =
      thetaAutomorphyFactor D a (thetaLatticeAction D b U) *
        thetaAutomorphyFactor D b U
  cocycle_relation_proved : cocycle_relation

/-- The factor cocycle structure is inhabited. -/
theorem thetaAutomorphyCocycle_holds {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : ThetaAutomorphyCocycle D where
  cocycle_relation := thetaAutomorphyFactor_cocycle D
  cocycle_relation_proved := thetaAutomorphyFactor_cocycle D

/-- The actual period relation on the unit group: V = r^a U for some a in Z. -/
def thetaPeriodRel {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U V : Lˣ) : Prop :=
  ∃ a : ℤ, V = (thetaRootUnit D) ^ a * U

/-- The period relation is an equivalence relation. -/
theorem thetaPeriodRel_equivalence {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : Equivalence (thetaPeriodRel D) where
  refl U := ⟨0, by simp [thetaRootUnit]⟩
  symm := by
    rintro U V ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    rw [zpow_neg]
    group
  trans := by
    rintro U V W ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a + b, ?_⟩
    rw [zpow_add]
    group

/-- Actual quotient base of the theta period lattice action. -/
def thetaPeriodSetoid {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : Setoid Lˣ :=
  ⟨thetaPeriodRel D, thetaPeriodRel_equivalence D⟩

/-- Actual quotient base. -/
def thetaPeriodBase {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : Type u :=
  Quot (thetaPeriodSetoid D)

/-- Actual quotient theta line bundle descent data: base is the period
quotient, cover is the unit group, fiber is L, automorphy is the actual theta
factor, and the section is oddTheta. -/
structure ThetaQuotientLineBundle
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) where
  base : Type u
  cover : Type u
  quotientMap : cover → base
  fiber : Type u
  automorphy : ℤ → cover → fiber → fiber
  section : cover → fiber
  section_automorphy : ∀ (a : ℤ) (U : cover),
    section ((thetaRootUnit D) ^ a * U) = automorphy a U (section U)

/-- Actual quotient theta line bundle with theta section. -/
noncomputable def thetaQuotientLineBundle {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : ThetaQuotientLineBundle D where
  base := thetaPeriodBase D
  cover := Lˣ
  quotientMap := Quot.mk (thetaPeriodSetoid D)
  fiber := L
  automorphy := fun a U c => thetaAutomorphyFactor D a (U : L) * c
  section := fun U => oddTheta D.q (U : L)
  section_automorphy := by
    intro a U
    exact thetaAutomorphy_shift D (U : L) (Units.ne_zero U) a

end ABCBridge.ThetaAutomorphyActual

end
