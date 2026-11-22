import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1QVMqFiberInterfaceActual
/-! Exact missing interfaces for the MqFiber/product-region bridge.  No
inhabitant is asserted. -/
/-- Fiber count of an index map `BadPlace → FPlace`. -/
def badFiberCount {BadPlace FPlace : Type*} (idx : BadPlace → FPlace) (i : FPlace) : Nat :=
  Nat.card { b : BadPlace // idx b = i }
/-- The bad/finite-place index bridge: fiber counts sum to the bad cardinality. -/
def BadFiberIndexBridge {BadPlace FPlace : Type*} [Fintype BadPlace] [Fintype FPlace]
    (idx : BadPlace → FPlace) : Prop :=
  (∑ i : FPlace, badFiberCount idx i) = Fintype.card BadPlace
/-- Correct discrete closed-ball log ratio at the q-region radius.  This
replaces the false all-radii `constant * r^degree` formula: in a
nonarchimedean field the closed-ball measure is constant between radii. -/
def ClosedBallLogRatioAtRpRadius (logBall unitBallLog localDim logp : Real) : Prop :=
  logBall - unitBallLog = -((localDim : Real) * logp)
/-- Donor record for the actual closed-ball Haar scaling. -/
def closedBallDonors : List String :=
  [ "Mzk1AnnulusMeasurePrimeActual.rootExtensionHaar_ball_ratio",
    "Mzk1HaarCylinderMeasureActual.rootExtensionHaar_closedBall_translate",
    "rootExtensionClosedBall_measure_pos", "rootExtensionClosedBall_measure_lt_top" ]
theorem closedBallDonors_length : closedBallDonors.length = 4 := rfl
#check badFiberCount
#check BadFiberIndexBridge
#check ClosedBallLogRatioAtRpRadius
#check closedBallDonors
end LeanFormal.IUT.XiFPaper.Mzk1QVMqFiberInterfaceActual
end