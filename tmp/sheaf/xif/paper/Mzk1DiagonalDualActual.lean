import tmp.sheaf.xif.paper.Mzk1DualIndexSourceActual
import tmp.sheaf.xif.paper.Mzk1DiagonalIndexActual

/-! CONDITIONAL: f-parameterized diagonal dual volume wrapper.
Definitions `coordSmall`/`coordDual` plus the volume ratio with explicit
quotient equivalence `φ` as input.  No sorry/axiom. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1DiagonalDualActual

open LeanFormal.IUT.XiFPaper.Mzk1DualIndexLinkActual
open LeanFormal.IUT.XiFPaper.Mzk1DualIndexSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual

variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]

def coordSmall : Submodule (PadicInt p) (d → ℚ_[p]) :=
  Submodule.pi Set.univ (fun _ => (1 : Submodule (PadicInt p) ℚ_[p]))

def coordDual (f : d → Nat) : Submodule (PadicInt p) (d → ℚ_[p]) :=
  Submodule.pi Set.univ (fun i =>
    Submodule.span (PadicInt p) {((p : ℚ_[p]) ^ (f i))})

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [MeasurableSpace E] [BorelSpace E]

theorem diagonal_dual_volume_ratio
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {L XG : AddSubgroup E} (hXGL : XG ≤ L)
    (hLc : IsCompact (L : Set E)) (hLo : IsOpen (L : Set E))
    (hXGc : IsCompact (XG : Set E)) (hXGo : IsOpen (XG : Set E))
    (hXGpos : μ (XG : Set E) ≠ 0) (hXGtop : μ (XG : Set E) ≠ ⊤)
    (f : d → Nat)
    (φ : (L ⧸ XG.comap L.subtype) ≃+
      ((d → PadicInt p) ⧸ diagLatticeSubmodule (p := p) (d := d) f)) :
    (μ (XG : Set E)).toReal / (μ (L : Set E)).toReal =
      (∏ i, (p : ℝ) ^ (f i))⁻¹ :=
  XG_volume_ratio_of_quotient_equiv (p := p) μ hXGL hLc hLo hXGc hXGo
    hXGpos hXGtop f φ

end LeanFormal.IUT.XiFPaper.Mzk1DiagonalDualActual
end