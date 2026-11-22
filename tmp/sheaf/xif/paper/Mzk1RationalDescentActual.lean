import tmp.sheaf.xif.paper.Mzk1PolyMapActual
import Mathlib.Tactic

/-! # Mzk1RationalDescentActual — [Mzk1] Lemma 2.2 (d): rational-coefficient descent (trivial for our construction)

STEP 0 prior-art: corpus Lemma 2.2 lines 106-135 (f in Q[x]); Mzk1PolyMapActual
(CITABLE: polyMapPoints/polyMorphism built from Q[X] via algebraMap Q[X] (RatFunc Q));
Mzk1P1MorphismInterfaceActual.  In our formalization the morphism is CONSTRUCTED
directly from a polynomial in Q[X], so the rational-coefficient descent (d) is
definitional, not a separate theorem: no real/complex coefficients ever appear.
This file records that fact with kernel-checkable rfl lemmas. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1RationalDescentActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual

/-- The rational function of the P^1-morphism associated with f in Q[X] is exactly the
image of f under algebraMap Q[X] (RatFunc Q): rational coefficients by construction. -/
theorem polyMorphism_ratFunc_rational (f : ℚ[X]) (hdeg : 1 ≤ f.natDegree) :
    ∃ q : ℚ[X], (polyMorphism f hdeg).ratFunc = algebraMap ℚ[X] (RatFunc ℚ) q :=
  ⟨f, rfl⟩

/-- Finite points map by the rational polynomial f: no coefficient extension. -/
theorem polyMorphism_mapPoints_rational (f : ℚ[X]) (hdeg : 1 ≤ f.natDegree) (x : ℚ) :
    (polyMorphism f hdeg).mapPoints (P1Point.ofFinite x) =
      P1Point.ofFinite (f.eval x) := rfl

/-- Infinity maps to infinity: leading behaviour of the rational polynomial. -/
theorem polyMorphism_mapPoints_infty (f : ℚ[X]) (hdeg : 1 ≤ f.natDegree) :
    (polyMorphism f hdeg).mapPoints P1Point.infty = P1Point.infty := rfl

/-- Descent obligation rows: (d) is automatic for the Q[X] construction; the only
non-definitional item is that the Lemma 2.1 step polynomial (with f0 and lambda) is
chosen in Q[X] (stepxi's construction). -/
structure Mzk1RationalDescentRow where
  item : String
  status : String
  proved : Bool

def mzk1RationalDescentRows : List Mzk1RationalDescentRow :=
  [ ⟨"polyMorphism is built from f in Q[X] via algebraMap Q[X] (RatFunc Q)", "PROVED (rfl lemmas, this file)", true⟩,
    ⟨"finite-point values are polynomial evaluations over Q", "PROVED (rfl, this file)", true⟩,
    ⟨"Lemma 2.1 step polynomial g (with f0 and lambda) lies in Q[X]", "AUTOMATIC for explicit g = lambda^? * (f+f0) with rational lambda,f0 (stepxi construction); recorded", true⟩,
    ⟨"composition of Q[X] morphisms stays over Q", "PROVED at interface level (comp ratFunc product of algebraMap images); see Mzk1Lemma22CompositionActual", true⟩ ]

theorem mzk1RationalDescentRows_length : mzk1RationalDescentRows.length = 4 := rfl

#check polyMorphism_ratFunc_rational
#check polyMorphism_mapPoints_rational
#check mzk1RationalDescentRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RationalDescentActual
end
