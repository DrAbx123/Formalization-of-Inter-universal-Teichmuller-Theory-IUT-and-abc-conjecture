import tmp.sheaf.xif.paper.Mzk1P5ComparisonDerivedActual

/-!
# phase exponent data: the last phase-specific named input

paperPhaseUnit m j = primitiveMu2lRoot.zeta^(m j) is already an actual mu2l
unit with phase_pow.  This file isolates the missing label-to-exponent map as
the explicit PhaseExponentData, and packages the resulting actual phase and
canonical comparison.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P5PhaseExponentDataActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeInstantiateActual
open LeanFormal.IUT.XiFPaper.Mzk1P5ComparisonDerivedActual
open LeanFormal.IUT.Foundations.Theta

universe v

/-- Explicit label -> mu2l phase exponent data. -/
structure PhaseExponentData (l : PrimeGeFive) where
  m : ThetaLabel (l := l) → Nat

variable {l : PrimeGeFive}
variable (P : PhaseExponentData l)

end LeanFormal.IUT.XiFPaper.Mzk1P5PhaseExponentDataActual
