import tmp.sheaf.xif.paper.Mzk1PolyChainRuleActual
import Mathlib.Tactic

/-! # Mzk1PolyUnramifiedCompositionActual — unramifiedness of composed polynomial P^1 maps

STEP 0 prior-art: corpus Lemma 2.2 lines 106-135; Mzk1PolyChainRuleActual (PROVED:
polyMapPoints_comp_finite/infty, polyUnramifiedAt_comp_finite, comp_ne_zero_of_nonconstant,
polyUnramifiedAt_comp_infty); Mzk1Lemma22CompositionActual (comp/PreservesSet/AvoidsPoint
composition); Mzk1PolyMapActual.  This file assembles the UnramifiedOver composition for
polynomial maps: if h is unramified over the complement of U, g over the complement of T,
and h maps T into U, then h.comp g is unramified over the complement of U. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PolyUnramifiedCompositionActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyChainRuleActual

/-- Unramifiedness is preserved by composition of polynomial maps (finite points and
infinity), with h mapping T into U. -/
theorem polyUnramifiedOver_comp {g h : ℚ[X]} (hgdeg : 1 ≤ g.natDegree) (hhdeg : 1 ≤ h.natDegree)
    {T U : Set (P1Point ℚ)}
    (hg : UnramifiedOver (polyMorphism g hgdeg) {p | p ∉ T} (polyUnramifiedAt g))
    (hh : UnramifiedOver (polyMorphism h hhdeg) {p | p ∉ U} (polyUnramifiedAt h))
    (hpres : PreservesSet (polyMorphism h hhdeg) T U) :
    UnramifiedOver
      (LeanFormal.IUT.XiFPaper.Mzk1Lemma22CompositionActual.comp
        (polyMorphism g hgdeg) (polyMorphism h hhdeg) hhdeg)
      {p | p ∉ U} (polyUnramifiedAt (h.comp g)) := by
  intro p hp
  cases p with
  | none =>
      have hpU : (none : P1Point ℚ) ∉ U := by
        simpa [LeanFormal.IUT.XiFPaper.Mzk1Lemma22CompositionActual.comp,
          polyMorphism, polyMapPoints] using hp
      have hT : (none : P1Point ℚ) ∉ T := by
        intro hmem
        have hres := hpres (none : P1Point ℚ) hmem
        exact hpU (by simpa [polyMorphism, polyMapPoints] using hres)
      have hhU : polyUnramifiedAt h (none : P1Point ℚ) :=
        hh (none : P1Point ℚ) (by simpa [polyMorphism, polyMapPoints] using hpU)
      exact polyUnramifiedAt_comp_infty hgdeg hhU
  | some x =>
      have hpU : P1Point.ofFinite (h.eval (g.eval x)) ∉ U := by
        simpa [LeanFormal.IUT.XiFPaper.Mzk1Lemma22CompositionActual.comp,
          polyMorphism, polyMapPoints, P1Point.ofFinite] using hp
      have hT : P1Point.ofFinite (g.eval x) ∉ T := by
        intro hmem
        have hres := hpres (P1Point.ofFinite (g.eval x)) hmem
        exact hpU (by simpa [polyMorphism, polyMapPoints, P1Point.ofFinite] using hres)
      have hgx : polyUnramifiedAt g (P1Point.ofFinite x) :=
        hg (P1Point.ofFinite x) (by simpa [polyMorphism, polyMapPoints, P1Point.ofFinite] using hT)
      have hhx : polyUnramifiedAt h (P1Point.ofFinite (g.eval x)) :=
        hh (P1Point.ofFinite (g.eval x))
          (by simpa [polyMorphism, polyMapPoints, P1Point.ofFinite] using hpU)
      exact polyUnramifiedAt_comp_finite hgx hhx

#check polyUnramifiedOver_comp

end LeanFormal.IUT.XiFPaper.Mzk1PolyUnramifiedCompositionActual
end
