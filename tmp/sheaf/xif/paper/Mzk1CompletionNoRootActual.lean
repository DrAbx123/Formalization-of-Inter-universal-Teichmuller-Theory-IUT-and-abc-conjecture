/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import Mathlib.Tactic

/-! # A935 hull: negative criterion for the completion root obstruction

`completionFirstFieldObstruction = Nonempty (NatRootSystem (concreteQUnit ...))`.
A `NatRootSystem u` gives all n-th roots, in particular a square root of u.
Therefore absence of a square root in the units refutes the obstruction.
This is a genuine negative theorem; the missing input for the concrete q unit
is exactly `no square root` (or the p-adic divisibility fact), not formalized here.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1CompletionNoRootActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual

/-- Generic negative criterion: no square root in the units => no NatRootSystem. -/
theorem no_natRootSystem_of_no_sqrt {M : Type*} [CommMonoid M] {u : Mˣ}
    (h : ¬ ∃ w : Mˣ, w ^ 2 = u) : ¬ Nonempty (NatRootSystem u) := by
  rintro ⟨r⟩
  apply h
  refine ⟨r.root 2, ?_⟩
  have h2 := r.compat 1 2 (by norm_num : (2 : Nat) ≠ 0)
  simpa [r.root_one] using h2

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- Concrete conditional negative theorem for the completion first field. -/
theorem completionFirstFieldObstruction_false_of_no_sqrt
    (h : ¬ ∃ w : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ,
      w ^ 2 = concreteQUnit (I := I) place) :
    ¬ completionFirstFieldObstruction (I := I) place := by
  unfold completionFirstFieldObstruction
  exact no_natRootSystem_of_no_sqrt h

def rows : List (String × String × String) :=
  [ ("no square root", "¬ ∃ w, w^2=u => ¬ Nonempty NatRootSystem u", "PROVED (no_natRootSystem_of_no_sqrt)"),
    ("concrete obstruction", "conditional negative theorem for concreteQUnit", "PROVED (completionFirstFieldObstruction_false_of_no_sqrt)"),
    ("missing input", "prove concreteQUnit has no square root (p-adic units)", "GAP") ]

theorem rows_length : rows.length = 3 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CompletionNoRootActual.no_natRootSystem_of_no_sqrt
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CompletionNoRootActual.completionFirstFieldObstruction_false_of_no_sqrt

end LeanFormal.IUT.XiFPaper.Mzk1CompletionNoRootActual

end