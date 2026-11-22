import Iut.Foundations.Orbicurve
open CategoryTheory
example (f g : Iut.signActionObject ⟶ Iut.signActionObject) : (f ≫ g).as = f.as * g.as := by rfl
example (f : Iut.signActionObject ⟶ Iut.signActionObject) (hf : f.as ≠ 1) : f.as = Multiplicative.ofAdd (1 : ZMod 2) := by
  revert f
  decide