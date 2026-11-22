import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import LeanFormal.IUT.Foundations.Theta.GaussianKernel

/-! # Semantic symbol types for the paper notation

Separates typographic symbols previously collapsed into one Lean identifier:
* `q_v` ONE underline under q: q-parameter;
* `q_v` TWO underlines under q: a 2l-th root of the q-parameter;
* theta labels are nonzero positive representatives j=1,...,l*, not all
  `SignedLabel` (j and -j give the same theta value).

The types are not definitionally equal. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual

universe u

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {place : FinitePlaceAtPrime K p}
variable {l : PrimeGeFive}

/-- Single-underlined q_v: actual q-parameter unit. -/
structure PaperQParameter where
  unit : (CommonPrimeCompletion place)ˣ

/-- Double-underlined q_v: a chosen 2l-th root of a q-parameter, with its base
q-parameter and exact power relation. -/
structure PaperQRoot where
  base : PaperQParameter (place := place)
  rootUnit : (AlgebraicClosure (CommonPrimeCompletion place))ˣ
  pow_twoL : rootUnit ^ (2 * l.value) =
    unitToAlgClosed base.unit

namespace PaperQRoot

theorem rootUnit_pow_twoL (R : PaperQRoot (place := place) (l := l)) :
    R.rootUnit ^ (2 * l.value) = unitToAlgClosed R.base.unit := R.pow_twoL

end PaperQRoot

/-- Nonzero positive theta labels j=1,...,l*; injective carrier. -/
abbrev PaperThetaLabel (l : PrimeGeFive) : Type :=
  {j : SignedLabel l.value // 0 < j.1}

namespace PaperThetaLabel

def toSignedLabel {l : PrimeGeFive} (j : PaperThetaLabel l) : SignedLabel l.value :=
  j.1

theorem toSignedLabel_injective {l : PrimeGeFive} :
    Function.Injective (toSignedLabel (l := l)) := by
  intro x y h
  apply Subtype.ext
  exact h

def value {l : PrimeGeFive} (j : PaperThetaLabel l) : Int := j.1.1

theorem value_pos {l : PrimeGeFive} (j : PaperThetaLabel l) : 0 < j.value :=
  j.2

def gaussExponent {l : PrimeGeFive} (j : PaperThetaLabel l) : Nat :=
  (LeanFormal.IUT.gaussExponent j.value).toNat

end PaperThetaLabel

end LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual

end
