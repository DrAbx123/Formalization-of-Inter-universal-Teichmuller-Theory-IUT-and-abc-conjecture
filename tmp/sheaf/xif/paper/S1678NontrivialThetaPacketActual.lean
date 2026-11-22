import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket

/-! # S1678: actual nontrivial theta packet and degree-faithful value action

Constructs an actual nontrivial theta packet q = 1/5 (not q=1), an actual
value monoid `Multiplicative Real`, the identity positive-real action, and the
identity degree map.  The degree of the actual q value is exactly `log(1/5)`,
so this is a nontrivial degree-faithful local value package.

EXACT REMAINING STRUCTURE: a source theater/family and `OriginalInput` whose
`thetaPacket` is this packet and whose prime-strip value monoid is this
`Multiplicative Real` monoid.  The current S1487/S1650 family fixes
`thetaPacket = ofQ 1` and `Mon = SourceHaarActualValueMonoid`; no source
family with the nontrivial packet/value monoid is built in the tree.

No q=1 data is presented as nontrivial, and no fake theater/family is built.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1678NontrivialThetaPacketActual

open LeanFormal.IUT

variable {l : PrimeGeFive}

/-- Actual nontrivial source theta packet q = 1/5. -/
noncomputable def S1678NontrivialThetaPacket : FiniteThetaPacket l :=
  FiniteThetaPacket.ofQ (l := l) ((5 : Real)⁻¹) (by norm_num)

@[simp] theorem S1678NontrivialThetaPacket_q :
    (S1678NontrivialThetaPacket (l := l)).q = (5 : Real)⁻¹ := rfl

theorem S1678NontrivialThetaPacket_q_ne_one :
    (S1678NontrivialThetaPacket (l := l)).q ≠ 1 := by
  rw [S1678NontrivialThetaPacket_q]
  norm_num

theorem S1678NontrivialThetaPacket_q_lt_one :
    (S1678NontrivialThetaPacket (l := l)).q < 1 := by
  rw [S1678NontrivialThetaPacket_q]
  norm_num

/-- Actual nontrivial value monoid: the multiplicative positive reals. -/
abbrev S1678ValueMonoid : Type :=
  Multiplicative Real

/-- Actual positive-real action on the value monoid: identity. -/
def S1678PositiveRealAction : Multiplicative Real →* S1678ValueMonoid :=
  MonoidHom.id (Multiplicative Real)

/-- Actual degree map: identity `Multiplicative Real →* Multiplicative Real`. -/
def S1678Degree : S1678ValueMonoid →* Multiplicative Real :=
  MonoidHom.id (Multiplicative Real)

@[simp] theorem S1678Degree_apply (x : S1678ValueMonoid) :
    S1678Degree x = x := rfl

@[simp] theorem S1678PositiveRealAction_apply (x : Multiplicative Real) :
    S1678PositiveRealAction x = x := rfl

/-- Degree-faithfulness at the actual q value: degree of the action at q is
exactly `log q`. -/
theorem S1678_degree_of_q :
    Multiplicative.toAdd (S1678Degree (S1678PositiveRealAction
      (Multiplicative.ofAdd (Real.log ((S1678NontrivialThetaPacket (l := l)).q))))) =
      Real.log ((S1678NontrivialThetaPacket (l := l)).q) := rfl

/-- The actual nontrivial local value package. -/
structure S1678NontrivialValuePackage where
  packet : FiniteThetaPacket l
  packet_q_ne_one : packet.q ≠ 1
  valueMonoid : Type
  [monoid : Monoid valueMonoid]
  action : Multiplicative Real →* valueMonoid
  degree : valueMonoid →* Multiplicative Real
  degree_of_q :
    Multiplicative.toAdd (degree (action
      (Multiplicative.ofAdd (Real.log packet.q)))) = Real.log packet.q

/-- Actual inhabitant of the nontrivial local value package. -/
noncomputable def S1678NontrivialValuePackageActual :
    S1678NontrivialValuePackage (l := l) where
  packet := S1678NontrivialThetaPacket
  packet_q_ne_one := S1678NontrivialThetaPacket_q_ne_one
  valueMonoid := S1678ValueMonoid
  action := S1678PositiveRealAction
  degree := S1678Degree
  degree_of_q := rfl

end LeanFormal.IUT.XiFPaper.S1678NontrivialThetaPacketActual

end
