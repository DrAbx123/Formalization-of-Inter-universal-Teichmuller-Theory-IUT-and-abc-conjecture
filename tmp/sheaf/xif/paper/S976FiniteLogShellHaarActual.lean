import tmp.sheaf.xif.paper.S970FiniteLogShellCarrierActual
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # S976: actual finite log-shell Haar data and self quotient bridge

On FiniteLogShellCarrier p d = Fin d -> Qp, the actual addHaar measure and the
closed unit ball give a FiniteLogShellHaarData with positive finite unit mass.
The finite carrier is Qp-linearly equivalent to itself, so the quotient bridge
is actual for this finite carrier.  For an arbitrary paper tensor packet the
bridge remains the exact FiniteQuotientBridge condition (finite-dimensional Qp
model), not faked. -/

noncomputable section
open scoped BigOperators TensorProduct
open MeasureTheory
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual

open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual

variable {p : Nat} [Fact p.Prime]

noncomputable instance finiteLogShellMeasurableSpace (d : Nat) :
    MeasurableSpace (FiniteLogShellCarrier p d) :=
  borel (FiniteLogShellCarrier p d)

instance finiteLogShellBorelSpace (d : Nat) :
    BorelSpace (FiniteLogShellCarrier p d) := ⟨rfl⟩

/-- Actual Haar/log-volume data on Fin d -> Qp: addHaar and the unit ball. -/
noncomputable def finiteLogShellHaarData (d : Nat) :
    FiniteLogShellHaarData (p := p) d where
  locallyCompactSpace := inferInstance
  measurableSpace := borel (FiniteLogShellCarrier p d)
  borelSpace := ⟨rfl⟩
  measure := Measure.addHaar
  isAddHaar := inferInstance
  unitRegion := Metric.closedBall (0 : FiniteLogShellCarrier p d) 1
  unit_pos := by
    exact Metric.measure_closedBall_pos (Measure.addHaar : Measure (FiniteLogShellCarrier p d))
      (0 : FiniteLogShellCarrier p d) (by norm_num)
  unit_lt_top := by
    exact (isCompact_closedBall (0 : FiniteLogShellCarrier p d) 1).measure_lt_top

/-- Actual Haar datum existence for every finite dimension. -/
theorem finiteLogShellHaarRequired (d : Nat) :
    FiniteLogShellHaarRequired (p := p) d :=
  ⟨finiteLogShellHaarData (p := p) d⟩

/-- Actual self quotient bridge for the finite carrier. -/
theorem finiteQuotientBridge_self (d : Nat) :
    FiniteQuotientBridge (p := p) (FiniteLogShellCarrier p d) :=
  ⟨d, ⟨LinearEquiv.refl ℚ_[p] (FiniteLogShellCarrier p d)⟩⟩

/-- For a finite-dimensional Qp packet, the bridge to a finite coordinate
carrier is actual via a chosen basis. -/
theorem finiteQuotientBridge_of_finiteDimensional
    (Packet : Type) [AddCommGroup Packet] [Module ℚ_[p] Packet]
    [FiniteDimensional ℚ_[p] Packet] :
    FiniteQuotientBridge (p := p) Packet := by
  classical
  let d := Module.finrank ℚ_[p] Packet
  let b := Module.finBasis ℚ_[p] Packet
  exact ⟨d, ⟨b.equivFun⟩⟩

/-- Exact bridge condition for a packet without a chosen finite Qp structure. -/
def S976FiniteQuotientBridgeRequired
    (Packet : Type) [AddCommGroup Packet] [Module ℚ_[p] Packet] : Prop :=
  FiniteQuotientBridge (p := p) Packet

end LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual

end
