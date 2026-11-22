import tmp.sheaf.xif.paper.S1395TorsionCardinalityPortActual

/-! Independent consumer check for S1395.  This file is not source; it only
imports the compiled S1395 module, re-checks the exported interfaces and
records their axiom footprints. -/

open LeanFormal.IUT.XiFPaper.S1395TorsionCardinalityPortActual

#check @zsmulFiber
#check @natCard_zsmulFiber_eq_natCard_torsionBy
#check @natCard_zsmulFiber_zero
#check @natCard_torsionBy_neg
#check @natCard_torsionBy_one
#check @natCard_torsionBy_neg_one
#check @natCard_zsmul_fiber_eq_card_torsionBy
#check @TorsionCardinalityAt
#check @card_zsmul_fiber
#check @torsionCardinalityAt_iff_card_fiber
#check @finite_torsionBy_of_torsionCardinalityAt
#check @natCard_torsionBy_prime
#check @card_zsmul_fiber_prime
#check @torsionCardinalityAt_one
#check @torsionCardinalityAt_neg_one

#print axioms zsmulFiber
#print axioms natCard_zsmulFiber_eq_natCard_torsionBy
#print axioms natCard_zsmulFiber_zero
#print axioms natCard_torsionBy_neg
#print axioms natCard_torsionBy_one
#print axioms natCard_torsionBy_neg_one
#print axioms natCard_zsmul_fiber_eq_card_torsionBy
#print axioms TorsionCardinalityAt
#print axioms card_zsmul_fiber
#print axioms torsionCardinalityAt_iff_card_fiber
#print axioms finite_torsionBy_of_torsionCardinalityAt
#print axioms natCard_torsionBy_prime
#print axioms card_zsmul_fiber_prime
#print axioms torsionCardinalityAt_one
#print axioms torsionCardinalityAt_neg_one
