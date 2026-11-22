import tmp.sheaf.n8.closure.EtaCommonShellUnitsNonempty

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaAdditiveCommonShellComparison

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellUnitsNonempty
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual additive common shell (image of the F-place logShell in the
common algebraic closure). -/
abbrev additiveCommonShell : Set (PadicAlgCl (nativePrime X)) :=
  fShellImage X

theorem additiveCommonShell_zero :
    (0 : PadicAlgCl (nativePrime X)) ∈ additiveCommonShell X :=
  zero_mem_fShellImage X

/-- Actual additive logMap image: the additive unit log of the F-shell units,
transported into the common carrier by the actual embedding. -/
noncomputable def additiveUnitLogMapImage : Set (PadicAlgCl (nativePrime X)) :=
  (fun u : (fPlaceShell X).Units =>
    fCompletionToPadicAlgCl X ((fPlaceShell X).logMap u).toAdd) '' Set.univ

/-- The same image as the embedding of the shell `unitLayer`. -/
noncomputable def additiveUnitLayerImage : Set (PadicAlgCl (nativePrime X)) :=
  (fun y => fCompletionToPadicAlgCl X y) '' (fPlaceShell X).unitLayer

theorem additiveUnitLogMapImage_eq :
    additiveUnitLogMapImage X = additiveUnitLayerImage X := by
  ext x
  constructor
  · rintro ⟨u, -, rfl⟩
    exact ⟨((fPlaceShell X).logMap u).toAdd, ⟨u, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, Set.mem_univ u, rfl⟩

/-! ## Additive comparison target -/

/-- Corrected additive comparison: the unit-log image is contained in the
additive common shell.  This is exactly the codomain Kummer containment
condition of `SourceLogShellDatum`, transported through the actual
embedding; it is not assumed. -/
def EtaAdditiveUnitLogComparison : Prop :=
  additiveUnitLogMapImage X ⊆ additiveCommonShell X

/-! ## Exact action gap -/

/- The root-system log-link action is defined on the algebraic-closure unit
group.  The additive common shell has no constructed transport from that
unit action, and the common shell units can fail to be nonempty (see
`EtaCommonShellUnitsNonempty`).  Therefore no additive action on
`additiveCommonShell` is asserted here; the missing declaration is an actual
additive log-link transport/compatibility map from the root-system layer to
the F-shell additive carrier. -/
def EtaAdditiveActionUnitsObstruction : Prop :=
  ¬ EtaCommonShellUnitsNonempty X

end LeanFormal.IUT.N8Closure.EtaAdditiveCommonShellComparison
