import tmp.sheaf.xif.paper.Mzk1DualIndexLinkActual
import tmp.sheaf.xif.paper.Mzk1DualTransposeActual

/-!
# X_G quotient source: diagonal equivalence ⇒ volume ratio

This file gives the explicit-source version of the `hq` input used in
`Mzk1DualIndexLinkActual`: if the quotient `L ⧸ X_G` is explicitly equivalent
to the diagonal quotient `(d → Z_p) ⧸ ∏ p^{e_i}`, then the cardinal is
`∏ i, p^{e_i}` and the conditional dual-volume ratio applies.

The actual construction of that quotient equivalence from the trace-dual
`X_G = (G · Z_p^r)^#` (and the comap formula in `Mzk1DualTransposeActual`)
is still a named GAP; no such equivalence is assumed silently here.

No sorry/axiom.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1DualIndexSourceActual

open LeanFormal.IUT.XiFPaper.Mzk1DualIndexLinkActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual

variable {p : ℕ} [Fact p.Prime]
variables {d : Type} [Fintype d] [DecidableEq d]

/-- A quotient type equivalent to the diagonal quotient has cardinal
`∏ i, p^{e_i}` (diagonal index theorem + `Nat.card_congr`). -/
theorem natCard_of_diagQuotient_equiv {Q : Type*} (e : d → ℕ)
    (φ : Q ≃ ((d → PadicInt p) ⧸ diagLatticeSubmodule (p := p) (d := d) e)) :
    Nat.card Q = ∏ i, p ^ (e i) := by
  calc
    Nat.card Q = Nat.card ((d → PadicInt p) ⧸
        diagLatticeSubmodule (p := p) (d := d) e) := Nat.card_congr φ
    _ = ∏ i, p ^ (e i) := natCard_quotient_diagLatticeSubmodule (p := p) (d := d) e

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [MeasurableSpace E] [BorelSpace E]

/-- Explicit-source form of the dual-volume ratio: the quotient equivalence
`L ⧸ X_G ≃ (d → Z_p) ⧸ ∏ p^{e_i}` supplies `hq`. -/
theorem XG_volume_ratio_of_quotient_equiv
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {L XG : AddSubgroup E} (hXGL : XG ≤ L)
    (hLc : IsCompact (L : Set E)) (hLo : IsOpen (L : Set E))
    (hXGc : IsCompact (XG : Set E)) (hXGo : IsOpen (XG : Set E))
    (hXGpos : μ (XG : Set E) ≠ 0) (hXGtop : μ (XG : Set E) ≠ ⊤)
    (e : d → ℕ)
    (φ : (L ⧸ XG.comap L.subtype) ≃+
      ((d → PadicInt p) ⧸ diagLatticeSubmodule (p := p) (d := d) e)) :
    (μ (XG : Set E)).toReal / (μ (L : Set E)).toReal =
      (∏ i, (p : ℝ) ^ (e i))⁻¹ :=
  dual_volume_ratio_of_quotient_cardinality (p := p) μ hXGL hLc hLo hXGc hXGo
    hXGpos hXGtop e (natCard_of_diagQuotient_equiv e φ.toEquiv)

end LeanFormal.IUT.XiFPaper.Mzk1DualIndexSourceActual

end