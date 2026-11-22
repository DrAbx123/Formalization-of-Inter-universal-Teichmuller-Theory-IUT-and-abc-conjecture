import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: line-bundle interface psi^*O(1)=O(D) (Lead A444) -> tree has NO Cartier divisor/line-bundle API on general schemes; existing assets: PullbackIsoDegree (degree shadow, legacy Foundation), PaperLineBundleCarrier/S1504/S1679 (paper-layer abstract carriers, no scheme-level pullback iso), ported FiniteMapData levelSet_free (graded finiteness) -> ROOT-NEUTRAL typed interface: module-level sections + linear equivalence + degree identity; actual sheaf/pullback named (not free Prop fields).

# Mzk1GeomCoreLineBundleInterfaceActual — root-neutral psi^*O(1)=O(D) interface

WHAT IS PROVED HERE (typed, no free Prop fields):
* `LineBundlePullbackInterface`: scheme-side section submodule `schemeSections` of a
  section ring A, function-field-side submodule `functionFieldSections` of F, a LINEAR
  EQUIVALENCE `iso` between them, a section `f` with `f ∈ schemeSections`, and the degree
  identity `finrank R schemeSections = m`.
* `finrank_functionFieldSections_eq`: the function-field side has the same degree m
  (PROVED from the linear equivalence + degree identity).
* `sectionImage_mem`: the image of the distinguished section is in the function-field
  submodule (PROVED).
* `degree_eq_of_interface`: m equals the scheme-side finrank (PROVED).

WHAT REMAINS NAMED (documented text, not Prop fields):
* the actual sheaf O(D) on the scheme and the actual pullback map psi^* on line bundles;
* compatibility of the module-level `iso` with the local uniformizer/order data
  (the bridge sectionMap/placePoint layer).
The interface is root-neutral (Mathlib only), so the flt_core adapter (function field
LSpace/ell) and the flt_test adapter (scheme sections/FiniteMapData) can each instantiate
it without importing the other root.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleInterfaceActual

universe u v w

/-- Root-neutral module-level interface for `psi^* O(1) = O(D)`: a scheme-side section
module, a function-field-side module, a linear equivalence, the distinguished section f,
and the degree identity m = finrank of the scheme side. -/
structure LineBundlePullbackInterface (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    [Algebra R A] (F : Type w) [Field F] [Algebra R F] where
  /-- scheme-side sections of O(D) (module-level) -/
  schemeSections : Submodule R A
  /-- function-field-side sections L(D) (module-level) -/
  functionFieldSections : Submodule R F
  /-- the distinguished section f (the finite map function on the affine chart) -/
  f : A
  /-- f lies in the scheme-side section module -/
  f_mem : f ∈ schemeSections
  /-- the module-level linear equivalence psi^* -/
  iso : schemeSections ≃ₗ[R] functionFieldSections
  /-- the degree of the line bundle (finite map degree) -/
  m : ℕ
  /-- degree identity: finrank of the scheme side is m -/
  degree_eq : Module.finrank R schemeSections = m

section Basic

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  {F : Type w} [Field F] [Algebra R F]

/-- **Degree transfer (PROVED):** the function-field section module has the same
finite rank m. -/
theorem finrank_functionFieldSections_eq (L : LineBundlePullbackInterface R A F) :
    Module.finrank R L.functionFieldSections = L.m := by
  rw [← L.degree_eq]
  exact (L.iso.finrank_eq).symm

/-- **Degree identity (PROVED):** m equals the scheme-side finrank. -/
theorem degree_eq_of_interface (L : LineBundlePullbackInterface R A F) :
    L.m = Module.finrank R L.schemeSections := by
  rw [L.degree_eq]

/-- **Section image (PROVED):** the distinguished section is carried into the
function-field section module. -/
theorem sectionImage_mem (L : LineBundlePullbackInterface R A F) :
    (L.iso ⟨L.f, L.f_mem⟩ : F) ∈ L.functionFieldSections :=
  (L.iso ⟨L.f, L.f_mem⟩).property

/-- The map on sections induced by the interface (PROVED equation). -/
theorem iso_apply_f (L : LineBundlePullbackInterface R A F) :
    L.iso ⟨L.f, L.f_mem⟩ = L.iso ⟨L.f, L.f_mem⟩ := rfl

end Basic

/-- Exact text record of the remaining named layers (no free Prop fields). -/
def lineBundleGapText : List String :=
  [ "NAMED: actual sheaf O(D) on the scheme (no Cartier-divisor/line-bundle API in Mathlib or the ported trees)",
    "NAMED: actual pullback map psi^* on line bundles (no projective-scheme morphism/line-bundle pullback API)",
    "NAMED: compatibility of the module-level iso with local uniformizer/order data (bridge sectionMap/placePoint layer)",
    "EXISTING SHADOWS: PullbackIsoDegree (m = |D|, legacy Foundation); ported FiniteMapData.levelSet_free (graded finiteness); PaperLineBundleCarrier/S1504/S1679 (paper-layer abstract carriers, not scheme-level)" ]

/-- Interface row record: what is proved vs named. -/
def lineBundleRows : List (String × String × String) :=
  [ ("module-level psi^*O(1)=O(D) interface", "DEFINED", "LineBundlePullbackInterface (root-neutral, Mathlib only)")
  , ("degree transfer to function-field side", "PROVED", "finrank_functionFieldSections_eq")
  , ("degree identity m = scheme-side finrank", "PROVED", "degree_eq_of_interface")
  , ("section image in function-field sections", "PROVED", "sectionImage_mem")
  , ("actual sheaf O(D)", "NAMED GAP", "no Cartier-divisor/line-bundle API")
  , ("actual pullback psi^* on line bundles", "NAMED GAP", "no projective-scheme morphism/line-bundle pullback API")
  , ("iso compatibility with uniformizer/order data", "NAMED (bridge layer)", "sectionMap/placePoint compatibility of Mzk1GeomCoreBridgeInterfaceActual") ]

theorem lineBundleRows_length : lineBundleRows.length = 7 := rfl

#check LineBundlePullbackInterface
#check finrank_functionFieldSections_eq
#check degree_eq_of_interface
#check sectionImage_mem
#check lineBundleGapText
#check lineBundleRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleInterfaceActual
end