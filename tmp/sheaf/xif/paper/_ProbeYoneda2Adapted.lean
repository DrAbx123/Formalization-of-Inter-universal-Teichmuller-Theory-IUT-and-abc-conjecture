import Iut.Foundations.Orbicurve
open CategoryTheory
#check yoneda
#check yoneda.map
#check yoneda.obj
variable {F : Type} [Field F] (S X : Iut.SchemeOverField F) (m : S ⟶ X)
#check yoneda.map m
#check (yoneda.obj S : (Iut.SchemeOverField F)ᵒᵖ ⥤ Type _)
#check (yoneda.obj X : (Iut.SchemeOverField F)ᵒᵖ ⥤ Type _)