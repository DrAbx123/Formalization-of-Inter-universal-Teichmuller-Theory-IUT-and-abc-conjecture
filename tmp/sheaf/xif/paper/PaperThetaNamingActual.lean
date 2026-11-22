import tmp.sheaf.xif.paper.PaperC3ThetaValuesActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

-- Explicit qParameter / qRoot naming for paper theta.
--
-- Single-underline q_v is the q-parameter (completion q unit).  Double-underline
-- q_v is q_v^(1/2l).  Paper theta uses the double-underline root:
--   theta_j = qRoot_v^(j^2).
-- qParameter^(j^2) is only the q-parameter power, not paper theta.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaNamingActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaValuesActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

-- Single-underline q_v: q-parameter power (NOT paper theta).
noncomputable def paperQParameterPower
    (j : SignedLabel l.value) (v : V) : ThetaExtension (G := G) v :=
  paperQParameterThetaValue (G := G) j v

-- Double-underline q_v: the actual 2l-th root, giving paper theta.
noncomputable def paperQRootTheta
    (j : SignedLabel l.value) (v : V) : (RootExtension (G := G) v)ˣ :=
  paperRootThetaUnit (G := G) j v

-- Paper theta is the root-valued object, not the q-parameter power.
abbrev paperTheta := paperQRootTheta (G := G)

#check paperQParameterPower
#check paperQRootTheta
#check paperTheta

end LeanFormal.IUT.XiFPaper.PaperThetaNamingActual

end