import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

/-!
# qUnit naming audit and explicit aliases

The source-geometry field G.qUnit is the single-underline q-parameter unit
q_v (q-parameter data). It is not the double-underline paper root q_v.

Explicit names:
* qParameterUnit G v = G.qUnit v
* qRootUnit G j v = paperRootThetaUnit G j v (the actual 2l-th root value)

No mathematical object is changed; these are definitional aliases.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.QUnitNamingAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.N8Closure.C3Roots

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Single-underline q-parameter unit, definitionally G.qUnit. -/
abbrev qParameterUnit (v : V) : CompletionValueCarrier (G.place v) :=
  G.qUnit v

/-- Double-underline actual root Theta unit, definitionally paperRootThetaUnit. -/
abbrev qRootUnit (j : SignedLabel l.value) (v : V) :
    (RootExtension (G := G) v)ˣ :=
  paperRootThetaUnit (G := G) j v

/-- Naming equality for the q-parameter unit. -/
theorem qParameterUnit_eq (v : V) :
    qParameterUnit (G := G) v = G.qUnit v := rfl

/-- Naming equality for the q-root unit. -/
theorem qRootUnit_eq (j : SignedLabel l.value) (v : V) :
    qRootUnit (G := G) j v = paperRootThetaUnit (G := G) j v := rfl

/-- The 2l-th power of the actual qRootUnit is the embedded qParameterUnit power. -/
theorem qRootUnit_pow_twoL (j : SignedLabel l.value) (v : V) :
    ((qRootUnit (G := G) j v : (RootExtension (G := G) v)ˣ) :
        RootExtension (G := G) v) ^ (2 * l.value) =
      (unitToAlgClosed (G.qUnit v) : RootExtension (G := G) v) ^
        (gaussExponent j.1).toNat := by
  unfold qRootUnit
  exact congrArg Units.val
    (paperRootThetaUnit_pow_twoL (G := G) j v)

end LeanFormal.IUT.XiFPaper.QUnitNamingAuditActual
end
