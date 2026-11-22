import Iut.Foundations.Orbicurve
open CategoryTheory
example (f : Iut.signActionObject ⟶ Iut.signActionObject) : (f.as : Iut.SignGroup) = f.as := rfl
example (f g : Iut.signActionObject ⟶ Iut.signActionObject) : ((f ≫ g).as : Iut.SignGroup) = (f.as : Iut.SignGroup) * (g.as : Iut.SignGroup) := by
  rw [LocallyDiscrete.comp_as]
  rfl
example (f : Iut.signActionObject ⟶ Iut.signActionObject) (hf : f.as ≠ (1 : Iut.SignGroup)) : (f.as : Iut.SignGroup) = Multiplicative.ofAdd (1 : ZMod 2) := by
  revert f
  decide