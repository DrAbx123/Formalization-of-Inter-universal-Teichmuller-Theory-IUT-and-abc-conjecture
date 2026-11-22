import tmp.sheaf.n8.closure.C5Native

/-!
# Corrected actual-link SHE representation

The current C5 `SHERepresentation` hard-codes identity links; this file defines
and constructs the actual-link four-leg simultaneity square, independent of C9.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SHERepresentationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C5Native

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual-link SHE square, using four actual `fLinkAt 0 0 0 0` links. -/
structure SHERepresentationActual where
  square : SourceSimultaneousHolomorphicExpression
    (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 0 0)
    (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 0 0)
    (fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0))
    (fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0))
    (fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0))
    (fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0))

/-- The actual-link SHE square is inhabited. -/
noncomputable def sheRepresentationActual : SHERepresentationActual I where
  square := SourceSimultaneousHolomorphicExpression.ofCommutingLegs (by rfl)

theorem sheRepresentationActual_nonempty : Nonempty (SHERepresentationActual I) :=
  ⟨sheRepresentationActual I⟩

end LeanFormal.IUT.N8Closure.SHERepresentationActual