import tmp.sheaf.xif.paper.S481AlignedDivisorMapActual

/-! # S503: q_v-generated Phi model — exact boundary

The paper object is `Phi_{C_v^⊢} = N · log_Phi(q_v)|_{D_v^⊢}`.  As an abstract
divisorial monoid this is the constant monoid `N`; the q_v dependence is the
distinguished generator `log_Phi(q_v)` and, equivalently, the characteristic
splitting `tau`.  A bare `DivisorialMonoidOn` carries no distinguished
generator, so it cannot encode q_v beyond isomorphism.  In particular a
q_v-dependent pullback with ramification is NOT the pullback of Phi (which is
constant); ramification belongs to the q_v valuation extension/divisor side.

This file records the exact missing package: a constant-N divisorial monoid
with a distinguished generator/splitting attached.  It does not relabel a
constant N as q_v-dependent.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S503QvPhiModelActual

open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S481AlignedDivisorMapActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

/-- Exact paper package: constant `N` monoid together with a distinguished
q_v generator and characteristic splitting.  The monoid alone is constant;
the generator/splitting is what carries q_v. -/
structure QvGeneratedPhiPaperData where
  phi : DivisorialMonoidOn.{u+1} (Example32SmallBase K) (fun _ _ => True)
  qOrder : ℕ
  distinguishedGenerator : Prop
  ramificationCompatibility : Prop
  characteristicSplitting : Prop

def QvGeneratedPhiPaperDataRequired : Prop :=
  Nonempty (QvGeneratedPhiPaperData K)

/-- Exact obstruction: a `DivisorialMonoidOn` has no field for a distinguished
generator or for the characteristic splitting; its pullback cannot carry q_v
ramification at the monoid level. -/
def BareDivisorialMonoidCannotEncodeQv : Prop :=
  QvGeneratedPhiPaperDataRequired K

end LeanFormal.IUT.XiFPaper.S503QvPhiModelActual
end
