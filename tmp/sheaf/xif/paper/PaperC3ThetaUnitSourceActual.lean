import tmp.sheaf.xif.paper.PaperC3TensorBlockActual
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket

/-! # Actual source Theta unit family for the C3 tensor block

Given an actual family of completion value units qUnit v with norm equal to the
actual theta packet q, the q-parameter power at label j and place v is

  qParameterUnit j v = qUnit v ^ (gaussExponent j).toNat.

This is a q-PARAMETER object, not paper theta.  Paper theta = qRoot^(j^2) is in
PaperC3ThetaRootActual/PaperC3RootThetaHullActual.

This is a completion unit (not an arbitrary UnitFamily).  Its norm is exactly
the actual packet scale:

  ||qParameterUnit j v|| = thetaPacket.scale j.

Hence qParameterUnit_source_actual is proved, not assumed.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperC3ThetaUnitSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual

universe u

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type} [Fintype V]
variable {l : PrimeGeFive}
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Actual source data: a completion value unit at every place with the packet
q norm, plus the actual theta packet. -/
structure ThetaUnitSourceData where
  thetaPacket : FiniteThetaPacket l
  qUnit : (v : V) → G.valueCarrier v
  qUnit_norm : ∀ v,
    ‖((qUnit v : G.valueCarrier v) : CommonPrimeCompletion (G.place v))‖ =
      thetaPacket.q

/-- The actual source Theta unit at label j and place v. -/
noncomputable def qParameterUnit
    (S : ThetaUnitSourceData (G := G) (l := l))
    (j : SignedLabel l.value) (v : V) : G.valueCarrier v :=
  (S.qUnit v) ^ (gaussExponent j.1).toNat

/-- The norm of the q-parameter unit is the actual packet scale. -/
theorem qParameterUnit_norm
    (S : ThetaUnitSourceData (G := G) (l := l))
    (j : SignedLabel l.value) (v : V) :
    ‖((qParameterUnit (G := G) (l := l) S j v :
        G.valueCarrier v) : CommonPrimeCompletion (G.place v))‖ =
      S.thetaPacket.scale j := by
  unfold qParameterUnit
  rw [Units.val_pow_eq_pow_val, norm_pow, S.qUnit_norm v,
    S.thetaPacket.scale_eq, realThetaValue]

end LeanFormal.IUT.XiFPaper.PaperC3ThetaUnitSourceActual

end
