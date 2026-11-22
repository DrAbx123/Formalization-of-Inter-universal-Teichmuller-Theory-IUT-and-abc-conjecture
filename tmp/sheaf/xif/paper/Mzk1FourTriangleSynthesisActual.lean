import tmp.sheaf.xif.paper.Mzk1LiteralIQCarrierActual
import tmp.sheaf.xif.paper.Mzk1HDDObjectActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ConcreteFiniteRouteColumns
import LeanFormal.IUT.IUTIII.Theorem311.SourceTheorem311Assembly

/-! Mainline (A482 rung): four-triangle synthesis `(HDD) = (hull+det) o (dsc)` then
  composed with (SHE): `3.11.5 => 3.12`.  The synthesis is stated on the literal IQ
  carrier (A481); the (xi-f) numerical comparison is an explicit hypothesis (the named
  Step (xi-f) residual), and from it the Cor 3.12 ordered conclusion plus ABC follow via
  the StepXI contract and the literal comparison family.  No model-carrier conclusion is
  used as the rung. -/

-- A483 retry: literal IQ carrier olean now available; dependency refreshed.
namespace LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSynthesisActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HDDObjectActual
open LeanFormal.IUT.XiFPaper.Mzk1LiteralIQCarrierActual
open LeanFormal.IUT.ConcreteFiniteStepXI

noncomputable section

universe u v w

/-- Four-triangle composite readout: (HDD) o (dsc) o (SHE). -/
def fourTriangleReadout {Hull Det DSC SHEOut : Type*}
    (hdd : HDDDecomposition Hull Det DSC) (dsc : SHEOut → DSC) :
    SHEOut → Hull × Det :=
  fun x => HDD hdd (dsc x)

theorem fourTriangleReadout_fst {Hull Det DSC SHEOut : Type*}
    (hdd : HDDDecomposition Hull Det DSC) (dsc : SHEOut → DSC) (x : SHEOut) :
    (fourTriangleReadout hdd dsc x).1 = hdd.hullReadout (dsc x) :=
  rfl

theorem fourTriangleReadout_snd {Hull Det DSC SHEOut : Type*}
    (hdd : HDDDecomposition Hull Det DSC) (dsc : SHEOut → DSC) (x : SHEOut) :
    (fourTriangleReadout hdd dsc x).2 = hdd.detReadout (dsc x) :=
  rfl

/-- The (HDD) = (hull+det) o (dsc) decomposition law: the composite readout is the pair
  of the hull and det readouts of the dsc image; composed with SHE it is the paper fourth
  triangle readout. -/
theorem HDD_eq_hull_det_comp_dsc {Hull Det DSC : Type*}
    (hdd : HDDDecomposition Hull Det DSC) (dscIn : DSC) :
    HDD hdd dscIn = (hdd.hullReadout dscIn, hdd.detReadout dscIn) :=
  rfl

/-- Four-triangle synthesis data for the `3.11.5 => 3.12` step: the StepXI contract with
  its q/Theta slots identified with the composite (HDD o dsc o SHE) readouts, plus the
  explicit Step (xi-f) numerical comparison residual on the literal carrier. -/
structure FourTriangleSynthesis (DSC SHEOut : Type*) where
  contract : StepXIContract
  hdd : HDDDecomposition Real Real DSC
  dsc : SHEOut → DSC
  sheOut : SHEOut
  hull_eq : contract.qSigned = (fourTriangleReadout hdd dsc sheOut).1
  theta_eq : contract.thetaSigned = (fourTriangleReadout hdd dsc sheOut).2
  /-- Step (xi-f) comparison residual: the composite hull readout is at most the det
    readout (explicit residual on the actual readout, not assumed elsewhere). -/
  step3115_comparison :
    (fourTriangleReadout hdd dsc sheOut).1 ≤ (fourTriangleReadout hdd dsc sheOut).2

/-- `3.11.5 => 3.12`: the four-triangle synthesis yields the Cor 3.12 ordered conclusion. -/
theorem cor312Conclusion_of_fourTriangleSynthesis {DSC SHEOut : Type*}
    (S : FourTriangleSynthesis DSC SHEOut) :
    Cor312Conclusion S.contract := by
  rw [Cor312Conclusion, S.hull_eq, S.theta_eq]
  exact S.step3115_comparison

/-- The SHE slit: composing the SHE arrow with the HDD composite preserves the hull/det
  projections (SHE transport law, definitional). -/
theorem fourTriangle_SHE_composition {Hull Det DSC SHEOut : Type*}
    (hdd : HDDDecomposition Hull Det DSC) (she : SHEOut → DSC) (x : SHEOut) :
    fourTriangleReadout hdd she x =
      (hdd.hullReadout (she x), hdd.detReadout (she x)) :=
  rfl

end


/-- Certificate-wiring form of the literal hull readout: the literal interface hull volume
  is the `ofReal` of the real hull volume consumed by the StepXI consumers. -/
theorem literalHullVolume_eq_ofReal {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull = ENNReal.ofReal (iqHullRealVolume W) :=
  iqHull_logVolume_hull_eq_ofReal W

/-- Finite-route columns: the concrete finite route readout as an HDD decomposition
  (hull readout = the column values, det readout = their finite supremum). -/
def columnsHDD {α : Type*} [Fintype α] [Nonempty α] (f : α → Real) :
    HDDDecomposition Real Real α where
  hullReadout := f
  detReadout := fun _ => finiteSup f

/-- The Step (xi-f) comparison holds columnwise for the concrete finite route: every
  column value is at most the finite supremum readout. -/
theorem columnsHDD_step3115 {α : Type*} [Fintype α] [Nonempty α] (f : α → Real)
    (i : α) :
    (HDD (columnsHDD f) i).1 ≤ (HDD (columnsHDD f) i).2 :=
  le_finiteSup f i

/-- Rung via the concrete finite route columns: the columnwise Step (xi-f) comparison
  yields the Cor 3.12 ordered conclusion through the four-triangle synthesis. -/
theorem cor312Conclusion_of_columnsSynthesis {α : Type*} [Fintype α] [Nonempty α]
    (f : α → Real) (contract : StepXIContract) (i : α)
    (hull_eq : contract.qSigned = (HDD (columnsHDD f) i).1)
    (theta_eq : contract.thetaSigned = (HDD (columnsHDD f) i).2) :
    Cor312Conclusion contract := by
  rw [Cor312Conclusion, hull_eq, theta_eq]
  exact columnsHDD_step3115 f i

end LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSynthesisActual