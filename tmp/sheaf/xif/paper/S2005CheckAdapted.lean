import tmp.sheaf.xif.paper.S2005FprimeGroupActual

open LeanFormal.IUT.XiFPaper.S2005FprimeGroupActual
open LeanFormal.IUT.XiFPaper.S1993D5FiniteGroupBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1999S1993BridgeActual

#check @S2005_finrank
#check @S2005FprimeGroupStructure
#check @S2005QuadraticSubfields
#check @S2005_gal_card
#check @S2005E_finrank

example : Module.finrank ℚ S1720Field = 12 := S2005_finrank
example : S1993FprimeGroupStructure := S2005FprimeGroupStructure
example : S1993QuadraticSubfields := S2005QuadraticSubfields
example : S1993SplittingFieldH_eq ∧ S1993FprimeGroupStructure :=
  ⟨S1999SplittingFieldH_eq, S2005FprimeGroupStructure⟩
