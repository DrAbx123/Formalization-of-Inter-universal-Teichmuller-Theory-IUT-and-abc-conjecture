import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure

/-!
# Root extension / source algebraic-closure carrier equivalence

Both carriers are algebraic closures of the same normalized completion:
RootExtension uses CommonPrimeCompletion (= NormalizedCompletion), and
SourceAlgebraicClosure uses the same normalized completion.  The actual ring
equivalence is therefore the identity, and it maps the 2l-th root to the same
root and transports the root theta units to the source spectral-norm carrier.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Actual ring equivalence from the root extension to the source algebraic
closure carrier. -/
noncomputable def rootExtensionEquivRingEquiv (v : V) :
    RootExtension (G := G) v ≃+* SourceAlgebraicClosure (G.place v).val :=
  RingEquiv.refl _

/-- The equivalence is the identity on the common algebraic closure. -/
theorem rootExtensionEquivRingEquiv_apply (v : V) (x : RootExtension (G := G) v) :
    rootExtensionEquivRingEquiv (G := G) v x = x := rfl

/-- The induced unit equivalence. -/
noncomputable def rootExtensionEquivUnits (v : V) :
    (RootExtension (G := G) v)ˣ ≃*
      (SourceAlgebraicClosure (G.place v).val)ˣ :=
  Units.mapEquiv (rootExtensionEquivRingEquiv (G := G) v).toMulEquiv

/-- The equivalence sends the 2l-th root to the same 2l-th root in the source
algebraic closure. -/
theorem rootExtensionEquiv_twoLthRootAt (v : V) :
    rootExtensionEquivUnits (G := G) v (twoLthRootAt (G := G) v) =
      (twoLthRootAt (G := G) v) := Units.ext rfl

/-- The root unit maps to the source-carrier root unit. -/
theorem rootExtensionEquiv_paperRootThetaUnit
    (j : SignedLabel l.value) (v : V) :
    rootExtensionEquivUnits (G := G) v (paperRootThetaUnit (G := G) j v) =
      (paperRootThetaUnit (G := G) j v) := Units.ext rfl

/-- Norm of a root-extension element, computed in the source spectral-norm
carrier. -/
noncomputable def rootExtensionNorm (v : V) (x : RootExtension (G := G) v) : Real :=
  ‖(rootExtensionEquivRingEquiv (G := G) v x :
    SourceAlgebraicClosure (G.place v).val)‖

/-- Norm compatibility of the 2l-th root under the carrier equivalence. -/
theorem rootExtensionNorm_twoLthRootAt (v : V) :
    rootExtensionNorm (G := G) v (twoLthRootAt (G := G) v) =
      ‖((rootExtensionEquivUnits (G := G) v (twoLthRootAt (G := G) v) :
        (SourceAlgebraicClosure (G.place v).val)ˣ) : SourceAlgebraicClosure (G.place v).val)‖ := rfl

end LeanFormal.IUT.XiFPaper.PaperRootExtensionEquivActual

end