import tmp.sheaf.n8.closure.NativeSourceTorsionActual

/-! # NativeSourceTorsionGaps: actual torsion basis and exact missing fields

For D : SourceClauseC A S C B, the actual clause-(c) l-torsion basis is
available.  NativeSourceTorsionGaps additionally requires torsionLabel,
six-torsion independence, and l-torsion compatibility, which SourceClauseC
does not supply.  This file gives the actual basis and the conditional gap
constructor; the exact missing object is the three-field package below.

No fake label/prop; no audit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.InitialThetaSource.NativeTorsionGapsActualField

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceTorsion

universe u

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}
variable (D : SourceClauseC A S C B)

/-- Actual native l-torsion carrier. -/
abbrev actualNativeTorsionCarrier : Type u :=
  Multiplicative (A.curve.LTorsion l)

/-- Actual clause-(c) l-torsion basis. -/
noncomputable def actualNativeTorsionBasis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l :=
  D.torsion_basis

/-- Exact missing fields for NativeSourceTorsionGaps at D. -/
structure NativeTorsionGapsMissingFields where
  torsionLabel : actualNativeTorsionCarrier (A := A) (l := l) → Fin 6
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

/-- Construct NativeSourceTorsionGaps from the exact missing fields. -/
noncomputable def nativeSourceTorsionGapsOfFields
    (M : NativeTorsionGapsMissingFields (A := A) (l := l)) :
    NativeSourceTorsionGaps D where
  torsionLabel := M.torsionLabel
  sixTorsionIndependent := M.sixTorsionIndependent
  sixTorsionIndependent_proved := M.sixTorsionIndependent_proved
  lTorsionCompatible := M.lTorsionCompatible
  lTorsionCompatible_proved := M.lTorsionCompatible_proved

/-- Exact missing object. -/
def NativeTorsionGapsMissingRequired : Prop :=
  Nonempty (NativeTorsionGapsMissingFields (A := A) (l := l))

end LeanFormal.IUT.InitialThetaSource.NativeTorsionGapsActualField

end
