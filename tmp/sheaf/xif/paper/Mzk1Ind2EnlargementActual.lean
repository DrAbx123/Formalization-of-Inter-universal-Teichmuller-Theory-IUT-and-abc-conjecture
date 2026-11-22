/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.Tactic

/-! # Ind2/Ind3 orbit objects on the actual root extension (task-83 B)

| field | value |
|---|---|---|
| Status | PARTIAL: actual orbit definitions and the exact Ind3 all-field orbit theorem are proved; the Ind2 unit/lattice index and the base-block comparison are explicit GAPs. |
| Carrier | K = rootNormedExtension T b (PaperRootCompletionTensorActual:58-60), a finite intermediate field. |
| Source actions | ind2Act/ind3Act on S1902Carrier (Mzk1ThetaPilotObjectActual:90-101); this file isolates the orbit on K. |
| GAP | Ind2 index-1 needs rootsOfUnity integral-unit and O_L-lattice API; Ind3 all-field orbit has no finite O_L-index; base qVFam comparison has no trace/norm bridge. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ind2EnlargementActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The root extension carrier K = K_b(root_b). -/
abbrev rootExt : Type := rootNormedExtension T b

/-- Ind2 orbit of x: multiplication by a 2l-th root of unity. -/
def ind2Orbit (x : rootExt T b) : Set (rootExt T b) :=
  Set.range (fun ζ : rootsOfUnity (2 * l.value) (rootExt T b) =>
    ((ζ : (rootExt T b)ˣ) : rootExt T b) * x)

/-- Ind3 orbit of x: multiplication by every nonzero field element -/
def ind3Orbit (x : rootExt T b) : Set (rootExt T b) :=
  Set.range (fun u : (rootExt T b)ˣ => (u : rootExt T b) * x)

/-- The Ind3 orbit of a nonzero x is exactly the nonzero elements of K. -/
theorem ind3Orbit_eq_nonzero (x : rootExt T b) (hx : x ≠ 0) :
    ind3Orbit T b x = {y : rootExt T b | y ≠ 0} := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact mul_ne_zero (Units.ne_zero u) hx
  · intro hy
    refine ⟨Units.mk0 (y / x) (div_ne_zero hy hx), ?_⟩
    change (y / x : rootExt T b) * x = y
    exact div_mul_cancel₀ y hx

/-- Ind3 orbit is not a finite-index enlargement: it contains 1 for every x≠0. -/
theorem one_mem_ind3Orbit (x : rootExt T b) (hx : x ≠ 0) :
    (1 : rootExt T b) ∈ ind3Orbit T b x := by
  rw [ind3Orbit_eq_nonzero T b x hx]
  exact one_ne_zero

def rows : List (String × String × String) :=
  [ ("ind2Orbit", "2l-th root orbit on rootNormedExtension", "DEF"),
    ("ind3Orbit", "all-field-unit orbit on rootNormedExtension", "DEF"),
    ("ind3Orbit_eq_nonzero", "orbit = K^×", "PROVED"),
    ("one_mem_ind3Orbit", "1 in orbit", "PROVED"),
    ("Ind2 index=1", "needs roots integral-unit + O_L lattice", "GAP"),
    ("base-block index", "needs trace/norm/restriction bridge", "GAP") ]

theorem rows_length : rows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ind2EnlargementActual

end