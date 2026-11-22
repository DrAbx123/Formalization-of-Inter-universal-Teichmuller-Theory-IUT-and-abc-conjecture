import tmp.sheaf.xif.paper.S2570Rabin613ActualAdapted
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570F613IrreducibleFinalActualAdapted

open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

theorem F613_irreducible : Irreducible F613 := by
  have hunit : IsUnit (C (168 : ZMod 613)) := isUnit_C.mpr (by decide)
  have hassoc : Associated G F613 := by
    rw [G_eq_scaled]
    exact associated_unit_mul_left F613 (C (168 : ZMod 613)) hunit
  exact hassoc.irreducible LeanFormal.IUT.XiFPaper.S2570Rabin613ActualAdapted.G_irreducible

#print axioms F613_irreducible

end LeanFormal.IUT.XiFPaper.S2570F613IrreducibleFinalActualAdapted
end
