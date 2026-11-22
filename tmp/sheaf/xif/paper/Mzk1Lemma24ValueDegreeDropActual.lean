import tmp.sheaf.xif.paper.Mzk1Lemma24StepProviderActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# Mzk1Lemma24ValueDegreeDropActual — (S1b) ValueDegreeDropStatement PROVED

STEP 0 prior-art (reuse, no re-proof): Mzk1Lemma24StepProviderActual (ValueDegreeDropStatement
definition + s3135_criticalPoint_degree_drop = (S1a) PROVED: critical points have
[Q(x):Q] <= d0-1); Mathlib FieldTheory intermediate-field API:
* IntermediateField.adjoin.finrank (IsIntegral K x -> finrank K K(x) = (minpoly K x).natDegree),
* IntermediateField.adjoin.finiteDimensional,
* IntermediateField.finrank_le_of_le_right (F <= E -> finrank K F <= finrank K E),
* IntermediateField.mem_adjoin_simple_iff (x in K(alpha) iff x = aeval alpha r / aeval alpha s),
* Algebra.IsAlgebraic.isIntegral (AlgebraicClosure is algebraic/integral over Q).
Paper: [Mzk1] Lemma 2.4 (lines 195-199): if f0 = minpoly(alpha0), d0 = deg f0, and
x is a root of f0' then the VALUE alpha' = f0(x) has [Q(alpha'):Q] <= d0-1.

THIS FILE proves (S1b): alpha' = f0(x) lies in Q(x), so Q(alpha') <= Q(x); tower
degrees give deg(minpoly alpha') <= deg(minpoly x); (S1a) bounds deg(minpoly x) <= d0-1.
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24ValueDegreeDropActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24StepProviderActual

/-- Every aeval alpha p lies in the simple extension Q(alpha). -/
theorem aeval_mem_adjoin_simple (alpha : Qbar) (p : Polynomial ℚ) :
    Polynomial.aeval alpha p ∈ IntermediateField.adjoin ℚ ({alpha} : Set Qbar) := by
  rw [IntermediateField.mem_adjoin_simple_iff]
  exact ⟨p, 1, by simp⟩

/-- **(S1b) ValueDegreeDropStatement PROVED:** [Q(f0(x)) : Q] <= d0 - 1 at critical x. -/
theorem valueDegreeDrop_proved : ValueDegreeDropStatement := by
  intro alpha0 x h0 hx
  have hS1a : (minpoly ℚ x).natDegree ≤ (minpoly ℚ alpha0).natDegree - 1 :=
    s3135_criticalPoint_degree_drop alpha0 x (by omega) hx
  -- integrality over Q (AlgebraicClosure is algebraic, hence integral)
  have hAlg : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  have hInt : Algebra.IsIntegral ℚ Qbar := Algebra.isAlgebraic_iff_isIntegral.mp hAlg
  have hintx : IsIntegral ℚ x := hInt.isIntegral x
  have hintalpha : IsIntegral ℚ (Polynomial.aeval x (minpoly ℚ alpha0)) :=
    hInt.isIntegral _
  -- the two simple extensions
  let Fx : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ ({x} : Set Qbar)
  let Fa : IntermediateField ℚ Qbar :=
    IntermediateField.adjoin ℚ ({Polynomial.aeval x (minpoly ℚ alpha0)} : Set Qbar)
  have hmem : Polynomial.aeval x (minpoly ℚ alpha0) ∈ Fx :=
    aeval_mem_adjoin_simple x (minpoly ℚ alpha0)
  have hle : Fa ≤ Fx := by
    refine (IntermediateField.adjoin_le_iff).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hmem
  haveI hfin : FiniteDimensional ℚ Fx := IntermediateField.adjoin.finiteDimensional hintx
  have hfrx : Module.finrank ℚ Fx = (minpoly ℚ x).natDegree :=
    IntermediateField.adjoin.finrank hintx
  have hfra : Module.finrank ℚ Fa =
      (minpoly ℚ (Polynomial.aeval x (minpoly ℚ alpha0))).natDegree :=
    IntermediateField.adjoin.finrank hintalpha
  have hlefin : Module.finrank ℚ Fa ≤ Module.finrank ℚ Fx :=
    IntermediateField.finrank_le_of_le_right hle
  calc (minpoly ℚ (Polynomial.aeval x (minpoly ℚ alpha0))).natDegree
      = Module.finrank ℚ Fa := hfra.symm
    _ ≤ Module.finrank ℚ Fx := hlefin
    _ = (minpoly ℚ x).natDegree := hfrx
    _ ≤ (minpoly ℚ alpha0).natDegree - 1 := hS1a

/-- Alias for consumers: (S1b) is proved. -/
theorem s3135_valueDegreeDrop_proved : ValueDegreeDropStatement := valueDegreeDrop_proved

/-- FieldDegreeDropStatement follows from (S1a)+(S1b). -/
theorem fieldDegreeDrop_proved : FieldDegreeDropStatement := by
  intro d0 alpha0 x h0 hdeg hx
  have h := valueDegreeDrop_proved alpha0 x (by omega) hx
  rwa [hdeg] at h

/-- Rows: (component, evidence, status). -/
def valueDegreeDropRows : List (String × String × String) :=
  [ ("alpha' = f0(x) in Q(x) (via aeval)", "aeval_mem_adjoin_simple", "PROVED (Mathlib mem_adjoin_simple_iff)"),
    ("Q(alpha') <= Q(x)", "adjoin_le_iff + singleton membership", "PROVED"),
    ("finranks = minpoly natDegree", "IntermediateField.adjoin.finrank (integrality from AlgebraicClosure)", "PROVED (Mathlib)"),
    ("[Q(alpha'):Q] <= [Q(x):Q]", "IntermediateField.finrank_le_of_le_right + finiteDimensional", "PROVED (Mathlib)"),
    ("[Q(x):Q] <= d0-1 at critical x", "s3135_criticalPoint_degree_drop (S1a, abc)", "PROVED (reuse)"),
    ("ValueDegreeDropStatement (S1b)", "valueDegreeDrop_proved", "PROVED"),
    ("FieldDegreeDropStatement (S1 full)", "fieldDegreeDrop_proved", "PROVED") ]

theorem valueDegreeDropRows_length : valueDegreeDropRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Lemma24ValueDegreeDropActual

end
