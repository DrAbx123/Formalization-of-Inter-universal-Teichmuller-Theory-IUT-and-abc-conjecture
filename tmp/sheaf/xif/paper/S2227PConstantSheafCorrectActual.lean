import tmp.sheaf.xif.paper.S2206PConstantSheafActual
import Mathlib.CategoryTheory.Sites.SheafOfTypes

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2206PConstantSheafActual
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2227PConstantSheafCorrectActual

universe v u

/-- The general refutation statement: on a site where the empty sieve is a
cover of some object X, a constant presheaf with two distinct global sections is
not a sheaf.  The empty family has every global section as an amalgamation, so
uniqueness fails. -/
def S2227ConstantPresheafNotSheafStatement : Prop :=
  forall {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (X : C),
    (⊥ : Sieve X) ∈ J X ->
      forall {A : Type} (a b : A), a ≠ b ->
        ¬ Presheaf.IsSheaf J ((Functor.const Cᵒᵖ).obj A)

/-- The concrete slice-site condition: the empty sieve is a cover of the
terminal object of the slice site over S. -/
def S2227SliceEmptyCover (S : Iut.SchemeOverField S1726K) : Prop :=
  (⊥ : Sieve (Over.mk (𝟙 S))) ∈
    ((Iut.SchemeOverField.etaleTopology S1726K).over S) (Over.mk (𝟙 S))

/-- The exact first missing for refuting the literal constant presheaf P0:
membership of the empty sieve at the terminal slice object. -/
def S2227FirstMissing (S : Iut.SchemeOverField S1726K) : Prop :=
  S2227SliceEmptyCover S

/-- The alternative correct P route: constant sheaf via HasWeakSheafify. -/
def S2227CorrectPFirstMissing (S : Iut.SchemeOverField S1726K) : Prop :=
  S2192HasWeakSheafify S

end LeanFormal.IUT.XiFPaper.S2227PConstantSheafCorrectActual

end
