import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import LeanFormal.IUT.ABCBridge.Galois.EllipticPrimeTorsionGalois

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.ABCBridge.Galois
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2769PointCardActual

open WeierstrassCurve

local instance S2769FactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Finite affine points over a finite field: zero or a nonsingular affine point. -/
def S2769PointEquivOption (W : WeierstrassCurve F) :
    W.toAffine.Point ≃
      Option {p : F × F // W.toAffine.Equation p.1 p.2 ∧
        W.toAffine.Nonsingular p.1 p.2} where
  toFun P := match P with
    | .zero => none
    | .some x y h => some ⟨(x, y), h.1, h⟩
  invFun o := match o with
    | none => .zero
    | some p => .some p.1.1 p.1.2 p.2.2
  left_inv P := by cases P <;> rfl
  right_inv o := by rcases o with _ | ⟨⟨x, y⟩, h⟩ <;> rfl

noncomputable instance S2769FintypePoint (W : WeierstrassCurve F) :
    Fintype W.toAffine.Point := by
  classical
  exact Fintype.ofEquiv _ (S2769PointEquivOption W).symm

/-- Cardinality of the 5-torsion subgroup from its ZMod 5-rank: if the
`ZMod 5`-dimension is 2, then `#E[5] = 5^2 = 25`. -/
theorem S2769_fiveTorsion_card
    (W : WeierstrassCurve F)
    (h : Module.finrank (ZMod 5) (torsionSubgroup W 5) = 2) :
    Nat.card (torsionSubgroup W 5) = 5 ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 5) (V := torsionSubgroup W 5),
    ZMod.card, h]

#check S2769_fiveTorsion_card
#print axioms S2769_fiveTorsion_card

end LeanFormal.IUT.XiFPaper.S2769PointCardActual
end
