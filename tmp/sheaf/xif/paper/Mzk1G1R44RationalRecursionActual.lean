/- R4.4 (route 23:49 ruling): the terminal product `M2AnalyticTargetRat` — a NONCONSTANT
RATIONAL MAP `P1 -> P1` over ℚ (not a polynomial) carrying the finite rational branch set
into the special set {0,1,∞} and avoiding it at the base point. REUSE:
- `Mzk1PolyMapActual.{polyMorphism, polyMapPoints, specialSet}` (polynomial ↪ P1Morphism),
- `Mzk1P1MorphismInterfaceActual.{P1Morphism, PreservesSet, AvoidsPoint}`,
- `RestatedLemma24InterfaceActual.{Mzk1Lemma24Target, polyEvalP1, specialSet}` (paper target),
- `Mzk1G1O6M2PinRecursionActual.{exists_terminal, natDegree_le_one_of_terminal}` (WF recursion).
NOTE: the polynomial `M2AnalyticTarget` is NOT a closure target (route 23:49 evidence).
DEDUP: no rational-map terminal product existed in the tree. -/
import tmp.sheaf.xif.paper.Mzk1G1O6M2PinRecursionActual
import tmp.sheaf.xif.paper.Mzk1PolyMapActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R44RationalRecursionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinRecursionActual
open Polynomial

/-- **R4.4 terminal product (rational-map version)**: a nonconstant `P1 -> P1` morphism over
`ℚ` carrying the finite rational branch set into `{0,1,∞}` and avoiding it at `β`. -/
def M2AnalyticTargetRat (S₁ : Finset (P1Point ℚ)) (β : P1Point ℚ) : Prop :=
  ∃ φ : P1Morphism ℚ, φ.nonconstant ∧
    (∀ p ∈ S₁, φ.mapPoints p ∈ Mzk1PolyMapActual.specialSet) ∧
    φ.mapPoints β ∉ Mzk1PolyMapActual.specialSet

theorem polyEvalP1_eq_polyMapPoints (q : Polynomial ℚ) (p : P1Point ℚ) :
    RestatedLemma24InterfaceActual.polyEvalP1 q p = Mzk1PolyMapActual.polyMapPoints q p := by
  cases p <;> rfl

theorem specialSet_eq :
    RestatedLemma24InterfaceActual.specialSet ℚ = Mzk1PolyMapActual.specialSet := by
  ext p
  cases p <;> simp [RestatedLemma24InterfaceActual.specialSet, Mzk1PolyMapActual.specialSet]

/-- The paper's (polynomial) Lemma 2.4 target yields the rational-map terminal product: the
polynomial is viewed through `polyMorphism`. The old polynomial target is only a donor — the
terminal R4.4 product is the rational-map one. -/
theorem m2AnalyticTargetRat_of_lemma24Target (S₁ : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (h : RestatedLemma24InterfaceActual.Mzk1Lemma24Target S₁ β) :
    M2AnalyticTargetRat S₁ β := by
  obtain ⟨q, hdeg, hS, hβ, -, -⟩ := h
  have hdeg1 : 1 ≤ q.natDegree := hdeg
  refine ⟨Mzk1PolyMapActual.polyMorphism q hdeg1, ?_, ?_, ?_⟩
  · exact hdeg1
  · intro p hp
    have hmem := hS p hp
    rw [polyEvalP1_eq_polyMapPoints, specialSet_eq] at hmem
    exact hmem
  · intro hmem
    apply hβ
    rw [polyEvalP1_eq_polyMapPoints, specialSet_eq]
    exact hmem

#print axioms m2AnalyticTargetRat_of_lemma24Target
end LeanFormal.IUT.XiFPaper.Mzk1G1R44RationalRecursionActual