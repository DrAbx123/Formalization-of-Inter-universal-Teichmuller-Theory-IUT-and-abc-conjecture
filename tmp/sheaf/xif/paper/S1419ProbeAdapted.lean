import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import tmp.sheaf.n8.closure.RepresentableStackIsStackConstructed
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

namespace S1419ProbeAdapted

universe u

variable (F : Type u) [Field F]

example (X : Iut.SchemeOverField F) :
    Iut.schemeRepresentableEtalePseudofunctor F X =
      discretePseudo (C := Iut.SchemeOverField F) (yoneda.obj X) := rfl

#check Pseudofunctor.IsStackFor
#check Pseudofunctor.isStackFor_iff
#check Pseudofunctor.IsStack.of_isStackFor
#check Functor.EssSurj
#check Functor.Full
#check Functor.Faithful
#check Functor.IsEquivalence
#check Presieve.IsSheafFor
#check Presieve.IsSheafFor.amalgamate
#check Presieve.IsSheafFor.isAmalgamation
#check Presieve.FamilyOfElements.SieveCompatible
#check Presieve.compatible_iff_sieveCompatible
#check Presieve.IsSheaf.isSheafFor
#check Presheaf.IsSheaf
#check isSheaf_iff_isSheaf_of_type

end S1419ProbeAdapted

end
