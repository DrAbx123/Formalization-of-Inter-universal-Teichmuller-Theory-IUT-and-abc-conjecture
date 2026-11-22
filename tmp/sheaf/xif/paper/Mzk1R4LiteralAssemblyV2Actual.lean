import tmp.sheaf.xif.paper.Mzk1LiteralIQHullFinitenessActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ConcreteFiniteRouteColumns

/-! Mainline (A484 rung R4 single assembly): the fourth triangle `(HDD) o (SHE)` on the
  literal global IQ carrier.  Self-contained: consumes the literal global IQ interface
  (S2723 through the hull-finiteness rung), the literal hull log-volume finiteness, the
  `(HDD) = (hull+det) o (dsc)` decomposition data with the explicit Step (xi-f)
  comparison residual, and the per-epsilon literal comparisons.  Concludes the Cor 3.12
  ordered conclusion, conditional ABC, and the literal hull log-volume finiteness.
  No value-model carrier is used. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1R4LiteralAssemblyV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S2723GlobalIQHullActual
open LeanFormal.IUT.XiFPaper.Mzk1LiteralIQHullFinitenessActual
open LeanFormal.IUT.ConcreteFiniteStepXI
open MeasureTheory

noncomputable section

/-- HDD decomposition data: hull and determinant readouts of the dsc image. -/
structure HDDDecomp (Hull Det DSC : Type*) where
  hullReadout : DSC → Hull
  detReadout : DSC → Det

/-- The (HDD) readout `(hull+det) o dsc`. -/
def HDD {Hull Det DSC : Type*} (d : HDDDecomp Hull Det DSC) : DSC → Hull × Det :=
  fun x => (d.hullReadout x, d.detReadout x)

theorem HDD_fst {Hull Det DSC : Type*} (d : HDDDecomp Hull Det DSC) (x : DSC) :
    (HDD d x).1 = d.hullReadout x := rfl

theorem HDD_snd {Hull Det DSC : Type*} (d : HDDDecomp Hull Det DSC) (x : DSC) :
    (HDD d x).2 = d.detReadout x := rfl

/-- Composition with (SHE): `(HDD) o (dsc) o (SHE)`. -/
def fourTriangleReadout {Hull Det DSC SHEOut : Type*}
    (d : HDDDecomp Hull Det DSC) (dsc : SHEOut → DSC) : SHEOut → Hull × Det :=
  fun x => HDD d (dsc x)

/-- Four-triangle synthesis data for `3.11.5 => 3.12`: the StepXI contract with its
  q/Theta slots identified with the composite `(HDD) o (dsc) o (SHE)` readouts and the
  explicit Step (xi-f) comparison residual. -/
structure FourTriangleSynthesis (DSC SHEOut : Type*) where
  contract : StepXIContract
  hdd : HDDDecomp Real Real DSC
  dsc : SHEOut → DSC
  sheOut : SHEOut
  hull_eq : contract.qSigned = (fourTriangleReadout hdd dsc sheOut).1
  theta_eq : contract.thetaSigned = (fourTriangleReadout hdd dsc sheOut).2
  step3115_comparison :
    (fourTriangleReadout hdd dsc sheOut).1 ≤ (fourTriangleReadout hdd dsc sheOut).2

/-- `3.11.5 => 3.12`: Cor 3.12 ordered conclusion from the four-triangle synthesis. -/
theorem cor312Conclusion_of_fourTriangleSynthesis {DSC SHEOut : Type*}
    (S : FourTriangleSynthesis DSC SHEOut) : Cor312Conclusion S.contract := by
  rw [Cor312Conclusion, S.hull_eq, S.theta_eq]
  exact S.step3115_comparison

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, Fintype (C3.tensorPlaceIndex i)]

/-- The literal global IQ interface (the actual `IQ(S±; n, D)` hull carrier). -/
def literalIQInterface (j : Nat) : IQHullLogVolumeInterface (GlobalIQAmbient (C3 := C3) j) :=
  globalIQHullInterface (C3 := C3) j

/-- Certificate-wiring form of the literal hull readout: the hull log-volume is the
  `ofReal` of the real hull volume consumed by the StepXI consumers. -/
theorem literalIQInterface_hull_logVolume_eq_ofReal (j : Nat) :
    (literalIQInterface (C3 := C3) j).logVolume (literalIQInterface (C3 := C3) j).hull =
      ENNReal.ofReal (iqHullRealVolume (literalIQInterface (C3 := C3) j)) :=
  iqHull_logVolume_hull_eq_ofReal _

/-- R4 single assembly: the fourth triangle `(HDD) o (SHE)` on the literal IQ carrier.
  Inputs: the literal per-epsilon comparison family (the two Cor 3.12 comparison clauses
  on the literal carrier) and the four-triangle synthesis data.  Outputs: Cor 3.12
  ordered conclusion, conditional ABC, and literal hull log-volume finiteness. -/
theorem r4_literal_assembly {DSC SHEOut : Type*}
    (S : FourTriangleSynthesis DSC SHEOut) (j : Nat)
    (hcomp : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison (literalIQInterface (C3 := C3) j) epsilon) :
    Cor312Conclusion S.contract ∧ ABCConjecture ∧
      globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ :=
  ⟨cor312Conclusion_of_fourTriangleSynthesis S,
   cor312ToABCBridge_abcConjecture
     { carrier := GlobalIQAmbient (C3 := C3) j
       hullData := literalIQInterface (C3 := C3) j
       epsilonComparison := hcomp },
   literalGlobalIQHull_logVolume_lt_top (C3 := C3) j⟩

/-- The finite-route columns give a columnwise Step (xi-f) comparison whose finite
  supremum readout matches the StepXI hull slot (ConcreteFiniteRouteColumns reuse). -/
theorem r4_finiteColumns_comparison {α : Type*} [Fintype α] [Nonempty α]
    (f : α → Real) (i : α) :
    (HDD (HDDDecomp.mk (fun j : α => f j) (fun _ : α => finiteSup f)) i).1 ≤
      (HDD (HDDDecomp.mk (fun j : α => f j) (fun _ : α => finiteSup f)) i).2 :=
  le_finiteSup f i

end

end LeanFormal.IUT.XiFPaper.Mzk1R4LiteralAssemblyV2Actual
-- A484 retry: forced mtime refresh after stale-content compile race.

-- A484 fix: Cor312EpsilonArithmeticComparison import (stepxi diagnosis).
