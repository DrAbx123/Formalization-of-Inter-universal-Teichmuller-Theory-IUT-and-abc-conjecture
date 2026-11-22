/- B1: monotonicity of the protected set `DTFixed` (selection of Tr).

  `DTFixed n T` is the chart-0 zero set of `prod (X - t)` over t in T, so enlarging T
  enlarges the protected set; consequently in the B1 selection step any superset of a
  certified Tr works. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1B2Fixed4Actual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1DTFixedMonoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual

variable (n : Nat)

/-- **`DTFixed` 单调**：`T ⊆ T'` ⇒ `DTFixed n T ⊆ DTFixed n T'`（Tr 选取可放大）。 -/
theorem DTFixed_mono {T T' : Finset ℚ} (h : T ⊆ T') :
    DTFixed n T ⊆ DTFixed n T' := by
  intro y hy
  obtain ⟨p, hp, rfl⟩ := hy
  exact Set.mem_image_of_mem _ (by
    obtain ⟨t, ht, hpt⟩ := hp
    exact ⟨t, h ht, hpt⟩)

/-- `DTFixed n ∅ = ∅`（空 T 保护集为空）。 -/
theorem DTFixed_empty : DTFixed n (∅ : Finset ℚ) = ∅ := by
  ext y
  constructor
  · rintro ⟨p, ⟨t, ht, _⟩, _⟩
    simpa using ht
  · intro hy
    simpa using hy

#print axioms DTFixed_mono
#print axioms DTFixed_empty

end LeanFormal.IUT.XiFPaper.Mzk1G1B1DTFixedMonoActual