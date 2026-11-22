import tmp.sheaf.xif.paper.Mzk1DiagEquivProvedActual

/-! GAP-step: quotient/cardinal for the diagonal dual chain.
`e'` maps `coordDualInt` to `coordDual.comap coordSmall.subtype`, giving
`(d→Z_p)/coordDualInt ≃ coordSmall/(coordDual.comap subtype)` and hence
cardinal `∏ p^{f_i}`.  No sorry/axiom. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1DiagQuotCardActual

open LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagEquivProvedActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual

variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]

theorem integerProductEquiv_map_comap (f : d → Nat) :
    Submodule.map (integerProductEquiv (p := p) (d := d)).toLinearMap
        (coordDualInt (p := p) (d := d) f) =
      (coordDual (p := p) (d := d) f).comap
        (coordSmall (p := p) (d := d)).subtype := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Submodule.mem_comap]
    have hmem : embLinear (p := p) (d := d) x ∈ coordDual (p := p) (d := d) f := by
      rw [← embLinear_map_coordDualInt (p := p) (d := d) f]
      exact Submodule.mem_map_of_mem hx
    simpa [integerProductEquiv, toCoordSmall, embLinear] using hmem
  · intro hy; rw [Submodule.mem_comap] at hy
    have hmem : (y : d → ℚ_[p]) ∈ Submodule.map (embLinear (p := p) (d := d))
        (coordDualInt (p := p) (d := d) f) := by
      rw [embLinear_map_coordDualInt (p := p) (d := d) f]; exact hy
    obtain ⟨x, hx, hxeq⟩ := Submodule.mem_map.mp hmem
    refine ⟨x, hx, ?_⟩
    apply Subtype.ext
    simpa [integerProductEquiv, toCoordSmall, embLinear] using hxeq

noncomputable def diagQuotEquiv (f : d → Nat) :
    ((d → PadicInt p) ⧸ coordDualInt (p := p) (d := d) f) ≃ₗ[PadicInt p]
      (coordSmall (p := p) (d := d) ⧸
        (coordDual (p := p) (d := d) f).comap (coordSmall (p := p) (d := d)).subtype) :=
  Submodule.Quotient.equiv (coordDualInt (p := p) (d := d) f) _
    (integerProductEquiv (p := p) (d := d))
    (integerProductEquiv_map_comap (p := p) (d := d) f)

theorem natCard_quotient_coordSmall (f : d → Nat) :
    Nat.card (coordSmall (p := p) (d := d) ⧸
        (coordDual (p := p) (d := d) f).comap (coordSmall (p := p) (d := d)).subtype) =
      ∏ i, p ^ (f i) := by
  calc
    Nat.card (coordSmall (p := p) (d := d) ⧸
        (coordDual (p := p) (d := d) f).comap (coordSmall (p := p) (d := d)).subtype)
        = Nat.card ((d → PadicInt p) ⧸ coordDualInt (p := p) (d := d) f) :=
          (Nat.card_congr (diagQuotEquiv (p := p) (d := d) f).toEquiv).symm
    _ = ∏ i, p ^ (f i) :=
          natCard_quotient_diagLatticeSubmodule (p := p) (d := d) f

end LeanFormal.IUT.XiFPaper.Mzk1DiagQuotCardActual
end