import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual

noncomputable section
universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

#check C3LDonor (I := I) place
#check actualSourcePilotRegionDataL (I := I) place
