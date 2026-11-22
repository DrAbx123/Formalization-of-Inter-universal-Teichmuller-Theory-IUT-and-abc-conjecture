import Iut.Foundations.Orbicurve
open CategoryTheory
open CategoryTheory.Bicategory
set_option pp.all true
#check Iut.signActionGenerator
-- Try to see Hom type
example : (Iut.signActionGenerator : Iut.signActionObject ⟶ Iut.signActionObject) = ⟨Multiplicative.ofAdd (1 : ZMod 2)⟩ := rfl
