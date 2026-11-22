import tmp.sheaf.xif.paper.Mzk1P1SpecialSetActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1SpecialSetGeneralActual — general-field special set (real)

Real Lean (no sorry/axiom): the paper's special set {infinity, 0, 1} over an arbitrary field,
as a finite set with genuine membership/cardinality lemmas.  Chained over the existing
Mzk1P1SpecialSetActual (ℂ case); this is the field-general form used by Lemma 2.4's
good-map conclusion.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1SpecialSetGeneralActual

open LeanFormal.IUT.XiFPaper.Mzk1P1SpecialSetActual

/-- Special set {infinity, 0, 1} over an arbitrary field, as a finite set. -/
def specialSetFinset (K : Type*) [Field K] : Finset (P1Point K) :=
  {P1Point.infty, P1Point.ofFinite (0 : K), P1Point.ofFinite (1 : K)}

/-- Infinity belongs to the general special set. -/
theorem infty_mem_specialSetFinset (K : Type*) [Field K] :
    P1Point.infty ∈ specialSetFinset K := by
  simp [specialSetFinset]

/-- 0 belongs to the general special set. -/
theorem zero_mem_specialSetFinset (K : Type*) [Field K] :
    P1Point.ofFinite (0 : K) ∈ specialSetFinset K := by
  simp [specialSetFinset]

/-- 1 belongs to the general special set. -/
theorem one_mem_specialSetFinset (K : Type*) [Field K] :
    P1Point.ofFinite (1 : K) ∈ specialSetFinset K := by
  simp [specialSetFinset]

/-- The general special set has cardinality 3 (for 0 ≠ 1). -/
theorem specialSetFinset_card (K : Type*) [Field K] (h : (0 : K) ≠ 1) :
    (specialSetFinset K).card = 3 := by
  classical
  rw [specialSetFinset]
  simp [h]

/-- The set underlying the general special set is finite. -/
theorem specialSetOf_finite (K : Type*) [Field K] :
    (specialSetFinset K : Set (P1Point K)).Finite :=
  (specialSetFinset K).finite_toSet

#check specialSetFinset
#check specialSetFinset_card

end LeanFormal.IUT.XiFPaper.Mzk1P1SpecialSetGeneralActual
end
