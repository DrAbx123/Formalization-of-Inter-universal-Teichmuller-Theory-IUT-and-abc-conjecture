import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaCStage

/-! # Stage-4 host: concrete theta packet for the from-scratch model

Source anchors: IUT I, Definition 3.1 (theta data); IUT II theta values;
IUT I, Example 3.2, (iv) (Gaussian concrete arithmetic).

CONSUMER: qpilot's model skeleton needs the theta-packet slot of
`HodgeTheater` for the model.  The concrete Example 3.6 stage theater
`concreteInitialThetaCStageTheater l : HodgeTheater l (FinitePrimePlace 2 7)`
already carries an actual `FiniteThetaPacket` (the Gaussian packet of q-value
gaussianFiveThetaQ).  This file exposes it with the exact binder arguments and
its concrete value/scale formulas, so the skeleton can fill the packet slot
with an actual inhabitant rather than a placeholder.

LABEL: prerequisite component (theta data), NOT a paper object claim beyond the
concrete stage theater.  Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open scoped BigOperators

local instance lgpModelFivePrimeFact : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The concrete model Hodge theater of the Example 3.6 stage. -/
abbrev lgpModelHodgeTheater (l : PrimeGeFive) :
    HodgeTheater l (FinitePrimePlace 2 7) :=
  concreteInitialThetaCStageTheater l

/-- The concrete theta packet of the model Hodge theater. -/
def lgpModelThetaPacket (l : PrimeGeFive) : FiniteThetaPacket l :=
  (lgpModelHodgeTheater l).thetaPacket

/-- The model theta packet is the Gaussian packet of q-value gaussianFiveThetaQ. -/
theorem lgpModelThetaPacket_eq (l : PrimeGeFive) :
    lgpModelThetaPacket l =
      FiniteThetaPacket.ofQ (l := l) gaussianFiveThetaQ gaussianFiveThetaQ_pos := rfl

/-- The q-value of the model theta packet. -/
theorem lgpModelThetaPacket_q (l : PrimeGeFive) :
    (lgpModelThetaPacket l).q = gaussianFiveThetaQ := rfl

/-- The arithmetic of the model Hodge theater is the concrete Gaussian arithmetic. -/
theorem lgpModelHodgeTheater_arithmetic (l : PrimeGeFive) :
    (lgpModelHodgeTheater l).arithmetic =
      concreteGaussianInitialThetaArithmeticData l := rfl

/-- The log-volume formula of the model theta packet (concrete sum of scales). -/
theorem lgpModelThetaPacket_logVolume (l : PrimeGeFive) :
    (lgpModelThetaPacket l).logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  unfold lgpModelThetaPacket lgpModelHodgeTheater
  exact concreteInitialThetaCStageTheater_logVolume l

#check lgpModelHodgeTheater
#check lgpModelThetaPacket
#check lgpModelThetaPacket_eq
#check lgpModelThetaPacket_q
#check lgpModelHodgeTheater_arithmetic
#check lgpModelThetaPacket_logVolume

end LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketActual
end