import tmp.sheaf.n8.closure.EtaAdditiveCommonShellComparison
import tmp.sheaf.n8.closure.EtaKummerSourceDatumAtF

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaAdditiveUnitLogComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaAdditiveCommonShellComparison
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.EtaKummerSourceDatumAtF
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The F-shell image with its carrier type written explicitly, avoiding a
projection/abbreviation mismatch in the membership goal. -/
noncomputable def fShellImageExplicit : Set (PadicAlgCl (nativePrime X)) :=
  (fun x : (fSourceDatum X).K => fCompletionToPadicAlgCl X x) ''
    (fSourceDatum X).logShell

theorem fShellImageExplicit_eq :
    fShellImageExplicit X = additiveCommonShell X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- Actual additive comparison: every additive unit log of an F-shell unit
lies in the additive common shell.  This uses the production
`fSourceDatum_codomainKummerContained` (unitLayer ⊆ logShell) and the
actual embedding into the common algebraic closure. -/
theorem additiveUnitLogComparison_actual :
    EtaAdditiveUnitLogComparison X := by
  rintro x ⟨u, -, rfl⟩
  have hmem : ((fPlaceShell X).logMap u).toAdd ∈ (fSourceDatum X).logShell := by
    have h := fSourceDatum_codomainKummerContained X ⟨u, rfl⟩
    change (Multiplicative.toAdd ((fPlaceShell X).logMap u)) ∈
      (fSourceDatum X).logShell at h
    exact h
  have hx : fCompletionToPadicAlgCl X ((fPlaceShell X).logMap u).toAdd ∈
      fShellImageExplicit X :=
    ⟨((fPlaceShell X).logMap u).toAdd, hmem, rfl⟩
  rwa [fShellImageExplicit_eq] at hx

end LeanFormal.IUT.N8Closure.EtaAdditiveUnitLogComparisonActual
