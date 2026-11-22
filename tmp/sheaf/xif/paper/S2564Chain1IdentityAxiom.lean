import tmp.sheaf.xif.paper.S2564Chain1IdentityActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual

/-- The two target types, restated verbatim. -/
example : (X : (ZMod 613)[X]) ^ 613 - T1 = G * S0 := chain1_identity
example : G ∣ (X : (ZMod 613)[X]) ^ 613 - T1 := chain1_dvd

end LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual

/-! ## Axiom audit -/

#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_coeff_le_11
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_coeff_12_80
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_coeff_161_240
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_coeff_241_320
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_coeff_321_400
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.S0_coeff_eq_zero_of_gt
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.S0_natDegree_le
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.G_natDegree_le
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.lhs_natDegree_le
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.rhs_natDegree_le
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_identity
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_dvd
