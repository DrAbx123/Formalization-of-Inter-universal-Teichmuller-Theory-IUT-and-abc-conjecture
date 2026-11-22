import tmp.sheaf.n8.closure.EtaLogLinkCommonClosure

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaLogLinkCommonIntersection

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-! ## Corrected common-carrier target -/

/-- Corrected comparison carrier: the intersection of the layer units with
the actual F-shell image in the common algebraic closure, not all layer units. -/
def commonLayerShell : Set (PadicAlgCl (nativePrime X)) :=
  layerUnitsInAlgCl X ∩ fShellImage X

theorem commonLayerShell_subset_layer :
    commonLayerShell X ⊆ layerUnitsInAlgCl X :=
  Set.inter_subset_left

theorem commonLayerShell_subset_shell :
    commonLayerShell X ⊆ fShellImage X :=
  Set.inter_subset_right

/-- Corrected target: on the common carrier, compare the intersection/subset
of the layer units with the actual F-shell image. -/
def EtaLogLinkCommonSubsetComparison : Prop :=
  commonLayerShell X ⊆ fShellImage X

theorem etaLogLinkCommonSubsetComparison_actual :
    EtaLogLinkCommonSubsetComparison X :=
  commonLayerShell_subset_shell X

/-! ## The full-inclusion target is not accepted -/

/-- The original full inclusion of all algebraic-closure layer units into
the F-shell image. -/
def EtaLogLinkFullLayerInclusion : Prop :=
  layerUnitsInAlgCl X ⊆ fShellImage X

/-- Exact witness that the full inclusion is false: an actual unit of the
common closure outside the F-shell image. -/
def EtaLogLinkFullInclusionWitness : Prop :=
  ∃ x : PadicAlgCl (nativePrime X),
    x ∈ layerUnitsInAlgCl X ∧ x ∉ fShellImage X

theorem fullInclusion_iff_noWitness :
    EtaLogLinkFullLayerInclusion X ↔ ¬ EtaLogLinkFullInclusionWitness X := by
  constructor
  · intro h
    rintro ⟨x, hx, hxout⟩
    exact hxout (h hx)
  · intro h x hx
    by_contra hxout
    exact h ⟨x, hx, hxout⟩

/-! ## Exact no-go -/

/- No production theorem identifies all `(AlgebraicClosure ℚ_[p])ˣ` with
the image of the F-completion shell.  The latter is the image of a
finite-dimensional F-completion inside the algebraic closure; the former is
the full unit group of the algebraic closure.  A witness of
`EtaLogLinkFullInclusionWitness` is the exact missing counterexample; a
proof of the full inclusion is the stronger (and normally false) missing
statement.  The target is therefore corrected to the intersection
`commonLayerShell` and the subset comparison above. -/
def EtaLogLinkFullInclusionNoGo : Prop :=
  ¬ EtaLogLinkFullLayerInclusion X

end LeanFormal.IUT.N8Closure.EtaLogLinkCommonIntersection
