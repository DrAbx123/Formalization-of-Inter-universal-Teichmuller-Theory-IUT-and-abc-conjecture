import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual
import Mathlib.RingTheory.RootsOfUnity.Basic

noncomputable section
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual

namespace LeanFormal.IUT.XiFPaper.S2614WeilPairingInterfaceActual

universe u
variable {F : Type u} [Field F]

/-- The group of `l`-th roots of unity in the algebraic closure. -/
abbrev Mu (F : Type u) [Field F] (l : PrimeGeFive) : Type u :=
  rootsOfUnity l.value (AlgebraicClosure F)

/-- Minimal Weil pairing data on the actual `l`-torsion subgroup: an
alternating bi-additive pairing to `μ_l`.  This is an interface only; no
inhabitant is asserted. -/
structure WeilPairingData (X : PuncturedEllipticCurve F) (l : PrimeGeFive) where
  pairing : X.LTorsion l → X.LTorsion l → Mu F l
  alternating : ∀ x : X.LTorsion l, pairing x x = 1
  bilinear_left : ∀ x y z : X.LTorsion l,
    pairing (x + y) z = pairing x z * pairing y z
  bilinear_right : ∀ x y z : X.LTorsion l,
    pairing x (y + z) = pairing x y * pairing x z

#check WeilPairingData
#check Mu

end LeanFormal.IUT.XiFPaper.S2614WeilPairingInterfaceActual
end