import tmp.sheaf.n8.closure.EtaSourceActionLogLinkActual
import tmp.sheaf.n8.closure.EtaFPlaceNormalizedComparison
import Mathlib.NumberTheory.Padics.Complex

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open LeanFormal.IUT.N8Closure.EtaSourceActionLogLinkActual
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual F-completion embedded into the common p-adic algebraic closure.
The embedding is obtained from the algebraic-closure lift of the finite
F-completion over `Q_p`; it is not an arbitrary map. -/
noncomputable def fCompletionToPadicAlgCl :
    CommonPrimeCompletion (nativeFPlaceAtPrime X) →ₐ[ℚ_[nativePrime X]]
      PadicAlgCl (nativePrime X) :=
  IsAlgClosed.lift

/-- Image of the actual F-place shell in the common algebraic closure. -/
noncomputable def fShellImage : Set (PadicAlgCl (nativePrime X)) :=
  (fun x => fCompletionToPadicAlgCl X x) '' (fPlaceShell X).logShell

/-- Actual layer units as a subset of the common algebraic closure. -/
def layerUnitsInAlgCl : Set (PadicAlgCl (nativePrime X)) :=
  {x | ∃ u : (AlgebraicClosure ℚ_[nativePrime X])ˣ,
    (u : AlgebraicClosure ℚ_[nativePrime X]) = x}

/-! ## Carrier comparison target -/

/-- Exact common-carrier comparison: the log-link layer image at level `m` is
contained in the F-shell image.  This is the target equation on the common
carrier, not an arbitrary transport. -/
def EtaLogLinkShellImageIncluded : Prop :=
  layerUnitsInAlgCl X ⊆ fShellImage X

theorem fShellImage_nonempty : (fShellImage X).Nonempty := by
  refine ⟨fCompletionToPadicAlgCl X 0, ⟨0, ?_, rfl⟩⟩
  exact (fPlaceShell X).zero_mem_logShell

theorem fCompletionToPadicAlgCl_injective :
    Function.Injective (fCompletionToPadicAlgCl X) :=
  (fCompletionToPadicAlgCl X).injective

end LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
