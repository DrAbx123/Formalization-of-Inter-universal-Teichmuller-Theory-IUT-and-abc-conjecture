import tmp.sheaf.xif.paper.S522QvPhiRamificationModelActual

/-! # S569: qOrder/pi from the S522 ramification data

`R.e` is an arrow-indexed ramification index, not a canonical object-level
qOrder: only `R.e (𝟙 X) = 1` is fixed, and other choices depend on the arrow.
From `R.e` at a chosen arrow one gets an actual qOrder.  In the divisor
monoid `qvPhiRamificationModel R` the generator `1` is actual and generates
the carrier, but it is not an element of the Input rationalFunctions/O^triangle.
That last realization is the exact missing object.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S569QvOrderPiActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual

universe u
variable {K : Type u} [Field K]
variable (R : RamificationIndexData (K := K))

/-- qOrder read from the ramification index of a chosen arrow. -/
noncomputable def qOrderAtArrow {X Y : Example32SmallBase K} (f : X ⟶ Y) : ℕ :=
  (R.e f).val

theorem qOrderAtArrow_pos {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    0 < qOrderAtArrow (K := K) R f := (R.e f).pos

theorem qOrderAtArrow_id (X : Example32SmallBase K) :
    qOrderAtArrow (K := K) R (𝟙 X) = 1 :=
  congrArg PNat.val (R.e_id X)

/-- The divisor-monoid generator `π` (i.e. `1 ∈ N`) for the S522 phi. -/
noncomputable def piDivisor (X : Example32SmallBase K) :
    ((qvPhiRamificationModel (K := K) R).obj X).carrier := ULift.up 1

/-- Every divisor-monoid element is a natural multiple of `piDivisor`. -/
theorem piDivisor_generator (X : Example32SmallBase K)
    (y : ((qvPhiRamificationModel (K := K) R).obj X).carrier) :
    ∃ n : ℕ, y = n • piDivisor (K := K) R X := by
  rcases y with ⟨n⟩
  have h : n • piDivisor (K := K) R X = ULift.up n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [succ_nsmul, ih]
      apply ULift.ext
      rfl
  exact ⟨n, by rw [h]⟩

/-- Exact missing: realizing the same `π` in the Input rationalFunctions /
O^triangle, rather than only in the divisor monoid `N`. -/
structure QvPiInOTriangleData where
  rationalFunctions : Prop
  pi : Prop
  pi_is_divisor_generator : Prop
  unit_decomposition : Prop

def QvPiInOTriangleDataRequired : Prop :=
  Nonempty QvPiInOTriangleData

end LeanFormal.IUT.XiFPaper.S569QvOrderPiActual
end
