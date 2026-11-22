import tmp.sheaf.xif.paper.S2013RootHomSheafActual

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2013RootHomSheafActual

universe u
variable {K : Type u} [Field K] {l : Nat}

#check @S2013RootHomSheaf_holds
#check @S2013RootPrestackIsPrestack
#check @S2013RootPrestack_isPrestack
#check @S2013isStack_iff
#check @S2013presheafHom_isSheaf
#print axioms S2013RootHomSheaf_holds
#print axioms S2013isStack_iff
