import Iut.Foundations.Orbicurve
open CategoryTheory
#check (Iut.signActionGenerator.as)
#check (Iut.signActionGenerator.as : Iut.signActionObject.as ⟶ Iut.signActionObject.as)
#reduce (Iut.signActionObject.as)
#check (Iut.signActionObject.as : SingleObj Iut.SignGroup)
#check ((Iut.signActionObject.as : SingleObj Iut.SignGroup) ⟶ Iut.signActionObject.as)