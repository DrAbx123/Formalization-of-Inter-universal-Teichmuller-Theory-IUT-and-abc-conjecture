import tmp.sheaf.xif.paper.S2564Chain1Mid6Actual

noncomputable section
open Polynomial

open LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.S0_coeff_389
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.S0_coeff_400
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.S0_coeff_401
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.S0_coeff_480
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.S0_coeff_389_400
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.S0_coeff_401_480
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.chain1_coeff_401
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.chain1_coeff_412
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.chain1_coeff_413
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.chain1_coeff_440
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.chain1_coeff_479
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.chain1_coeff_480
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.chain1_mid6

/-- The exact target type of the task, at the agreed quantifier shape. -/
example : ∀ n : ℕ, 401 ≤ n → n ≤ 480 →
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n :=
  LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.chain1_mid6

end
