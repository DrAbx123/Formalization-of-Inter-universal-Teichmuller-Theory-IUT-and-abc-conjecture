import tmp.sheaf.xif.paper.S2574LocalizedP12Actual
import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2585FbarIdentificationActual

local instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

/-- The residue scalar c = residue of the inverse of the leading unit. -/
noncomputable def S2585c (W : S2584PrimeDegreeOneWitness) : ZMod 613 :=
  W.residueEquivS (Ideal.Quotient.mk W.P
    ((((S2574_lead_unit.unit)⁻¹ : Sˣ) : S)))

theorem S2585c_ne_zero (W : S2584PrimeDegreeOneWitness) : S2585c W ≠ 0 := by
  unfold S2585c
  apply IsUnit.ne_zero
  apply IsUnit.map (f := W.residueEquivS.toRingHom)
  exact IsUnit.map (f := Ideal.Quotient.mk W.P) (Units.isUnit _)

/-- fbar identification. -/
theorem S2585_fbar_map (W : S2584PrimeDegreeOneWitness) :
    (S2574f.map (Ideal.Quotient.mk W.P)).map W.residueEquivS.toRingHom =
      Polynomial.C (S2585c W) * F613 := by
  simp only [S2574f, S2574P, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map]
  rw [← RingHom.comp_assoc]
  have hcomp : (W.residueEquivS.toRingHom.comp (Ideal.Quotient.mk W.P)).comp
      (algebraMap ℤ S) = Int.castRingHom (ZMod 613) :=
    RingHom.ext_int _ _
  rw [hcomp]
  rw [show S2132Psi5Z.map (Int.castRingHom (ZMod 613)) = F613 from F613_eq_map.symm]
  rfl

#check S2585c
#check S2585_fbar_map
#print axioms S2585_fbar_map

end LeanFormal.IUT.XiFPaper.S2585FbarIdentificationActual
end
