import Mathlib.Algebra.Ring.Action.Basic

namespace Probe

variable {G : Type} [Group G] {A : Type} [CommRing A]

noncomputable def psi : G →* (A →+* A) := 1

noncomputable instance : MulSemiringAction G A := MulSemiringAction.compHom A psi

example (g : G) (x : A) : g • x = psi g x := rfl

end Probe
