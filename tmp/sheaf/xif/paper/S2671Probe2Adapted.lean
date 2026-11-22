import tmp.sheaf.xif.paper.S2670D9EssSurjActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2670D9EssSurjActual
variable {l : LeanFormal.IUT.PrimeGeFive} {F : Type} [Field F] (D : S2619ActionGroupoidData (l:=l) (F:=F))
#synth MulAction (S2619G l) (S2619Hom (l:=l) (F:=F) D (Opposite.op (S2666EmptyBase (F:=F))))
