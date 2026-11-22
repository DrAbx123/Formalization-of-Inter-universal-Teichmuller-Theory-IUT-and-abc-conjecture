import Mathlib

/-!
# Mzk1HDDObjectActualAdapted (adapted copy, A475 reuse) — Hull-determinant decomposition (HDD) data (genuine defininitions + projections)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Paper HDD = (hull+det) o dsc: a decomposition object with hull/det maps and combined readout;
projection lemmas are genuine. Registers DEF-level object only. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HDDObjectActualAdapted

/-- HDD decomposition data: a source type with hull and det readouts. -/
structure HDDDecomposition (Hull Det DSC : Type*) where
  hullReadout : DSC → Hull
  detReadout : DSC → Det

/-- Combined HDD readout (hull, det) o dsc. -/
def HDD {Hull Det DSC : Type*} (d : HDDDecomposition Hull Det DSC) : DSC → Hull × Det :=
  fun x => (d.hullReadout x, d.detReadout x)

/-- Genuine projection: first component of HDD is the hull readout. -/
theorem HDD_fst {Hull Det DSC : Type*} (d : HDDDecomposition Hull Det DSC) (x : DSC) :
    (HDD d x).1 = d.hullReadout x := rfl

/-- Genuine projection: second component of HDD is the det readout. -/
theorem HDD_snd {Hull Det DSC : Type*} (d : HDDDecomposition Hull Det DSC) (x : DSC) :
    (HDD d x).2 = d.detReadout x := rfl

end LeanFormal.IUT.XiFPaper.Mzk1HDDObjectActualAdapted
