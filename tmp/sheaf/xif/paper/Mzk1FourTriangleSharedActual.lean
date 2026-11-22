import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! A487 shared four-triangle definitions (unified B version, extracted verbatim from
  `Mzk1R4LiteralAssemblyActual` so all lanes can consume one type).
  No value-model carrier, no sorry/axiom. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual

open LeanFormal.IUT

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

end

end LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual