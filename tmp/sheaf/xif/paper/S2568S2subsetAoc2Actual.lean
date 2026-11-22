/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2566AdjoinIntegralCActual

/-!
# S2568: `S ⊆ Aoc2` when `Aoc2` is integrally closed

`Aoc2 = Algebra.adjoin R (HZc2.rootSet L) ⊆ L` is the order-`C` analogue of
`Aoc = Algebra.adjoin R (HZc.rootSet L)` from `S2557AdjoinIntegralActual`.
Assuming that `Aoc2` is a fraction ring of `L` and is integrally closed in it
(both hypotheses are explicit in the theorem, so this file is independent of
`S2567IsFractionRingAdjoinCActual`), every element of `S` lies in `Aoc2`.

The proof is the order-`C` transcript of `S2558ReverseReductionActual`:

* `S2555_isIntegralClosure : IsIntegralClosure S R L`, so `s : S` is integral
  over `R`;
* `IsIntegral.map` along `R → S → L` turns this into integrality of
  `algebraMap S L s` over `R`;
* `IsIntegral.tower_top` pushes it to integrality over `Aoc2`;
* `IsIntegrallyClosed.isIntegral_iff` writes the element as
  `algebraMap Aoc2 L y`, and `y.2` is exactly the required membership.

No `sorry`, no new axiom, no `True`/`native_decide` gate.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace LeanFormal.IUT.XiFPaper.S2568S2subsetAoc2Actual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual

/-- **`S ⊆ Aoc2` for an integrally closed order-`C` adjoining algebra.** -/
theorem S2_le_Aoc2_of_integrallyClosed
    [IsFractionRing Aoc2 L] (h : IsIntegrallyClosed Aoc2) :
    ∀ s : S, algebraMap S L s ∈ Aoc2 := by
  intro s
  haveI : IsIntegralClosure S R L := S2555_isIntegralClosure
  have hxR : IsIntegral R (algebraMap S L s) :=
    IsIntegral.map (IsScalarTower.toAlgHom R S L)
      (IsIntegralClosure.isIntegral (R := R) (A := S) (B := L) s)
  have hxA : IsIntegral Aoc2 (algebraMap S L s) := hxR.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Aoc2) (K := L)).mp hxA
  rw [← hy]
  exact y.2

#print axioms S2_le_Aoc2_of_integrallyClosed
end LeanFormal.IUT.XiFPaper.S2568S2subsetAoc2Actual
end
