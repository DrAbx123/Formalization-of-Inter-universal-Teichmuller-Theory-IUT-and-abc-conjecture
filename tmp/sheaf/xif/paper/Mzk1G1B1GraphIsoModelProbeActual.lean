/-
Probe 4: argument passing for IsLocalization.Away.lift (temporary)
-/
import tmp.sheaf.xif.paper.Mzk1G1B1SmoothCriterionSubmActual

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1B1SmoothCriterionSubmActual

namespace LeanFormal.IUT.XiFPaper.ProbeGIM4

abbrev ModelPoly : Type := MvPolynomial (Fin 2) (Polynomial ℚ)

-- sanity: named args on an ordinary lemma with explicit binders
theorem foo (a b : ℕ) : a + b = b + a := Nat.add_comm a b

example : 1 + 1 = 1 + 1 := foo (a := 1) (b := 1)

example : (3 : ℕ) + 4 = 4 + 3 := Nat.add_comm (n := 3) (m := 4)

#check @IsLocalization.Away.lift
#check @IsLocalization.Away.lift_eq
#check @IsLocalization.Away.liftAlgHom
#check @IsLocalization.Away.liftAlgHom_apply

-- explicit application, instances as underscores
example (h : Polynomial ℚ) (f : chartT h →+* smoothModelRing h)
    (hf : IsUnit (f (hDerivElt h))) :
    Localization.Away (hDerivElt h) →+* smoothModelRing h :=
  @IsLocalization.Away.lift (chartT h) _ (Localization.Away (hDerivElt h)) _ _
    (smoothModelRing h) _ (hDerivElt h) _ f hf

end LeanFormal.IUT.XiFPaper.ProbeGIM4
