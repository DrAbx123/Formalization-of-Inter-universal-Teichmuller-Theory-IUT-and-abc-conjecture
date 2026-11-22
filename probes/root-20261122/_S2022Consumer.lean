import tmp.sheaf.xif.paper.S2022QuotientStackActual

/-! Consumer check for S2022: the olean imports and its named interface is usable. -/

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S2002RootStackificationActual
open LeanFormal.IUT.XiFPaper.S2022QuotientStackActual

universe u

variable {K : Type u} [Field K] {l : PrimeGeFive}

#check @S2022QuotientStackPackage
#check @S2022FirstMissing
#check @S2022QuotientStackPackage.toRootStackification
#check @S2022QuotientStackPackage.prestack_iff_S2019FirstMissing
#check @S2022FirstMissing_implies_S1997
#check @S2022FirstMissing_implies_S1994
#check @S2019FirstMissing_implies_S2022FirstMissing
#check @S2022PhiEquiv
#check @S2022PhiTwistHomEquiv
#check @S2022PHS.twistEquivariantEquiv

example (h : S2022FirstMissing K l) : S1997RootStackificationMissing K l :=
  S2022FirstMissing_implies_S1997 h

example (D : S2022QuotientStackPackage K l) :
    S2002FaithfulAtOrigin D.quotient D.comparison :=
  D.faithfulAtOrigin

#print axioms S2022FirstMissing_implies_S1997
#print axioms S2022QuotientStackPackage.prestack_iff_S2019FirstMissing
