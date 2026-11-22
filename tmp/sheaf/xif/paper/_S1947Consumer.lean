import tmp.sheaf.xif.paper.S1947DomainWActual

open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1925ProjectiveClosureActual
open LeanFormal.IUT.XiFPaper.S1947DomainWActual

example : IsDomain W := S1947_isDomain_W
example : S1925DenseChart := S1947DenseChart
#check S1947_isDomain_W
#check S1947DenseChart
#print axioms S1947_isDomain_W
#print axioms S1947DenseChart
