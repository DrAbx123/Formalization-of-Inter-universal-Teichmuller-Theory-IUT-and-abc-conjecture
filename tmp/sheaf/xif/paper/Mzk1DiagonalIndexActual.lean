/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula
import Mathlib.LinearAlgebra.Quotient.Pi
import LeanFormal.IUT.Foundations.LocalFields.PadicIntegerProductLattice
import LeanFormal.IUT.Foundations.MeasureTheory.CompactOpenAddSubgroupIndex

/-!
# Cardinal of the diagonal coordinate quotient (task-109)

Self-contained cardinal lemma: the quotient of `(d → Z_p)` by the product
`∏ i, p^{e_i}Z_p` has cardinal `∏ i, p^{e_i}`.  This is the index input
for the diagonal product Haar scaling; the measure identity is a separate
gap (see coord/P3-MINIMAL-ACCEPTANCE.md §5b.2). -/

noncomputable section
open scoped BigOperators
open MeasureTheory
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual

open LeanFormal.IUT.PadicLatticeIndex

variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]

/-- The diagonal product lattice `∏ i, p^{e_i} Z_p` in `d → Z_p`. -/
noncomputable def diagLatticeSubmodule (e : d → Nat) :
    Submodule (PadicInt p) (d → PadicInt p) :=
  Submodule.pi Set.univ (fun i =>
    Ideal.span ({(p : PadicInt p) ^ (e i)} : Set (PadicInt p)))

/-- The quotient cardinal is the product of the coordinate quotient
cardinalities. -/
theorem natCard_quotient_diagLatticeSubmodule (e : d → Nat) :
    Nat.card ((d → PadicInt p) ⧸ diagLatticeSubmodule (p := p) e) =
      ∏ i, p ^ (e i) := by
  let q := Submodule.quotientPi (R := PadicInt p) (Ms := fun _ : d => PadicInt p)
    (p := fun i => Ideal.span ({(p : PadicInt p) ^ (e i)} : Set (PadicInt p)))
  rw [show diagLatticeSubmodule (p := p) e =
      Submodule.pi Set.univ (fun i =>
        Ideal.span ({(p : PadicInt p) ^ (e i)} : Set (PadicInt p))) from rfl]
  rw [Nat.card_congr q.toEquiv, Nat.card_pi]
  congr 1
  funext i
  exact natCard_quotient_span_padicInt_pow (p := p) (e i)

def diagIndexRows : List (String × String) :=
  [ ("diagLatticeSubmodule", "product p^e ideals"),
    ("natCard_quotient_diagLatticeSubmodule", "quotient cardinal"),
    ("measure scaling", "GAP") ]

theorem diagIndexRows_length : diagIndexRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual
