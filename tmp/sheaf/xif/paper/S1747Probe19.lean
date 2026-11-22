import Mathlib.RingTheory.Etale.Finite

open CategoryTheory CategoryTheory.Limits

namespace S1747Probe

variable {K : Type} [Field K]

example (T X : (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) (f : T ⟶ X) : True := by
  -- can we access f.unop's hom?
  have h1 := f.unop.hom
  have h2 := f.unop.hom.hom
  trivial

example (T X : CommAlgCat.FiniteEtale.{0} K) (f : T ⟶ X) : True := by
  have h1 := f.hom
  have h2 := f.hom.hom
  trivial

example (T X : CommAlgCat.FiniteEtale.{0} K) (f : T.obj ⟶ X.obj) : True := by
  let g : T ⟶ X := ObjectProperty.homMk f
  have h1 := g.hom
  trivial

end S1747Probe
