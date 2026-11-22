import tmp.sheaf.xif.paper.S2670D9EssSurjActual
open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2670D9EssSurjActual
variable {l : PrimeGeFive} {F : Type} [Field F] (D : S2619ActionGroupoidData (l:=l) (F:=F))
example : MulAction (S2619G l) (S2619Hom (l:=l) (F:=F) D (Opposite.op (S2666EmptyBase (F:=F)))) := inferInstance
