import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteF0ImageSelfActual — self-contained f0 image degree bound (real)

Real Lean (no sorry/axiom): f0 = minpoly does not increase the finite maximal degree;
self-contained (only the green Mzk1NestedInductionActual import).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageSelfActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_image_le_self (S : Finset Qbar) (f : Qbar -> Qbar) (M : Nat)
    (h : forall x, x ∈ S -> degQ (f x) <= M) :
    maxDeg (S.image f) <= M := by
  unfold maxDeg
  apply Finset.sup_le
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact h x hx

theorem maxDeg_f0Image_le_self (S : Finset Qbar) (alpha0 : Qbar) :
    maxDeg (S.image (fun x => aeval x (minpoly ℚ alpha0))) <= maxDeg S := by
  apply maxDeg_image_le_self
  intro x hx
  have hxle : degQ x <= maxDeg S := by
    unfold maxDeg
    exact Finset.le_sup hx
  exact le_trans (degQ_aeval_le (minpoly ℚ alpha0) x) hxle

theorem maxDeg_f0CritImage_le_self (alpha0 : Qbar) :
    maxDeg ((critSet alpha0).image (fun x => aeval x (minpoly ℚ alpha0))) <= degQ alpha0 := by
  apply maxDeg_image_le_self
  intro x hx
  have hroot := aeval_derivative_eq_zero_of_mem_critSet hx
  exact le_of_lt (degQ_critValue_lt alpha0 x hroot)

def finiteF0ImageSelfRows : List (String × String) :=
  [ ("maxDeg_f0Image_le_self", "PROVED"), ("maxDeg_f0CritImage_le_self", "PROVED") ]

theorem finiteF0ImageSelfRows_length : finiteF0ImageSelfRows.length = 2 := rfl

theorem numMax_le_card_self (S : Finset Qbar) : numMax S <= S.card := by
  unfold numMax
  exact Finset.card_filter_le _ _

theorem numMax_f0Image_le_self (S : Finset Qbar) (alpha0 : Qbar) :
    numMax (S.image (fun x => aeval x (minpoly ℚ alpha0))) <= S.card := by
  have h1 : numMax (S.image (fun x => aeval x (minpoly ℚ alpha0)))
      <= (S.image (fun x => aeval x (minpoly ℚ alpha0))).card :=
    numMax_le_card_self _
  have h2 : (S.image (fun x => aeval x (minpoly ℚ alpha0))).card <= S.card :=
    Finset.card_image_le
  omega

theorem maxDeg_image_eq_sup (S : Finset Qbar) (f : Qbar -> Qbar) :
    maxDeg (S.image f) = S.sup (fun x => degQ (f x)) := by
  unfold maxDeg
  rw [Finset.sup_image]

#check maxDeg_image_eq_sup

#check numMax_f0Image_le_self

#check maxDeg_f0Image_le_self

end LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageSelfActual
end
