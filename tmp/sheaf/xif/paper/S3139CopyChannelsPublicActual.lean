import tmp.sheaf.xif.paper.S3139C2FiniteCopyActionLightActual
import tmp.sheaf.xif.paper.S3139FirstTriangleFieldACResidualActual
import tmp.sheaf.xif.paper.S3139FieldCArchimedeanLogActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: public copy-action interface (archimedean + finite-place) for lattice/mainline

Public consumer interface of the first-triangle copy action: the complete
`SourceCopyActionChannels` record combines the archimedean channel (constructed
from the actual infinite-place data, `sourceArchimedeanCopyActionData`) with the
finite-place channel (constructed from the exact missing local element map and
fiber assignment, `sourceFinitePlaceCopyActionData`).  Both channels preserve the
splitting-monoid scalar action (their `SourceInd2CopyActionData` law).

**Component, not paper object.**  Named consumers: first-triangle mutation,
lattice/mainline q/Theta comparison and R1/M-fields.  No sorry/axiom/True/PUnit/
toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139CopyChannelsPublicActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldACResidualActual
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual
open LeanFormal.IUT.XiFPaper.S3139C2LocalDegreeDataActual
open LeanFormal.IUT.XiFPaper.S3139C2FiniteCopyActionLightActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The complete public copy-action interface of the first triangle at one
capsule level and valuation: archimedean (actual) + finite-place channels. -/
abbrev PublicCopyActionChannels
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (Dlgp : SourceLGPData Real l V I)
    {F : FPrimeStrip.{umon, uv, upi} V}
    (j : Fin (capsuleLevels l)) (vQ : Dlgp.capsule.VQ) :=
  SourceCopyActionChannels (F := F) I Dlgp j vQ

/-- The public interface is available whenever the exact missing finite-place
data (local element map + fiber assignment) and an infinite-place choice are
supplied; the archimedean channel inside is constructed from actual data. -/
noncomputable def publicCopyActionChannels
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (Dlgp : SourceLGPData Real l V I)
    {F : FPrimeStrip.{umon, uv, upi} V}
    (D : SourceFmodLocalElementMap  F
      I.initial.arithmetic)
    (j : Fin (capsuleLevels l)) (vQ : Dlgp.capsule.VQ)
    (arch : SourceInd2CopyActionData Real Dlgp j vQ
      (Capsule j.val → (I.initial.arithmetic.Fmod)ˣ))
    (σ : SourceCapsuleFiberAssignment (l := l) V j) :
    PublicCopyActionChannels (F := F) I Dlgp j vQ :=
  sourceCopyActionChannels (F := F) I Dlgp D j vQ arch σ

/-- Both channels of the public interface preserve the splitting-monoid scalar
action (the `SourceInd2CopyActionData` law, restated for consumers). -/
theorem publicCopyActionChannels_archimedean_scalar
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (Dlgp : SourceLGPData Real l V I)
    {F : FPrimeStrip.{umon, uv, upi} V}
    (D : SourceFmodLocalElementMap  F
      I.initial.arithmetic)
    (j : Fin (capsuleLevels l)) (vQ : Dlgp.capsule.VQ)
    (arch : SourceInd2CopyActionData Real Dlgp j vQ
      (Capsule j.val → (I.initial.arithmetic.Fmod)ˣ))
    (σ : SourceCapsuleFiberAssignment (l := l) V j)
    (u : Capsule j.val → (I.initial.arithmetic.Fmod)ˣ)
    (g : Dlgp.lgp.Carrier) (x : Dlgp.tensorPacket j vQ) :
    (publicCopyActionChannels (F := F) I Dlgp D j vQ arch σ).archimedean.action u
        ((Dlgp.actionOnTensorPacket j vQ) g x) =
      (Dlgp.actionOnTensorPacket j vQ) g
        ((publicCopyActionChannels (F := F) I Dlgp D j vQ arch σ).archimedean.action u x) :=
  (publicCopyActionChannels (F := F) I Dlgp D j vQ arch σ).archimedean.action_scalar u g x

end LeanFormal.IUT.XiFPaper.S3139CopyChannelsPublicActual

end
