import tmp.sheaf.xif.paper.NativeTorsionFieldsActual
import tmp.sheaf.n8.closure.NativeSourceTorsionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

/-! # NativeSourceTorsionGaps: actual lTorsionCompatible field

For a SourceNativeInitialThetaData T, the native source assembly uses

  NativeSourceTorsionGaps (A := T.arithmetic) (S := T.tuple.source)
    (C := T.clauseA) (B := T.clauseB) T.clauseC.

This file constructs the actual lTorsionCompatible field of that record from
the actual ClauseC l-coprime-to-bad-residue condition
nativeLTorsionCompatible (S := T.tuple.source), with its actual proof.

The remaining exact missing fields are one label map
Multiplicative (T.arithmetic.curve.LTorsion l) -> Fin 6 and the six-torsion
independence proposition with proof.  They are recorded only as a missing
structure; no arbitrary label/Prop/axiom is introduced.

No audit; only Lean defs/theorems. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeTorsionGapsSourceFieldsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceTorsion
open LeanFormal.IUT.XiFPaper.NativeTorsionFieldsActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Actual l-torsion compatibility for the native source T. -/
def sourceNativeLTorsionCompatible : Prop :=
  nativeLTorsionCompatible (S := T.tuple.source)

/-- Actual proof of l-torsion compatibility. -/
theorem sourceNativeLTorsionCompatible_proved :
    sourceNativeLTorsionCompatible T :=
  nativeLTorsionCompatible_proved (S := T.tuple.source)

/-- The actual l-torsion carrier at T. -/
abbrev sourceNativeTorsionCarrier : Type :=
  Multiplicative (T.arithmetic.curve.LTorsion l)

/-- NativeSourceTorsionGaps for T with the actual lTorsionCompatible field and
the two remaining source fields supplied as explicit inputs. -/
noncomputable def nativeSourceTorsionGapsActual
    (torsionLabel : sourceNativeTorsionCarrier (l := l) T → Fin 6)
    (sixTorsionIndependent : Prop)
    (sixTorsionIndependent_proved : sixTorsionIndependent) :
    NativeSourceTorsionGaps
      (A := T.arithmetic) (S := T.tuple.source)
      (C := T.clauseA) (B := T.clauseB) T.clauseC where
  torsionLabel := torsionLabel
  sixTorsionIndependent := sixTorsionIndependent
  sixTorsionIndependent_proved := sixTorsionIndependent_proved
  lTorsionCompatible := sourceNativeLTorsionCompatible T
  lTorsionCompatible_proved := sourceNativeLTorsionCompatible_proved T

/-- The exact two missing fields for the native torsion gaps. -/
structure NativeTorsionLabelAndIndependenceMissing where
  torsionLabel : sourceNativeTorsionCarrier (l := l) T → Fin 6
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent

/-- Exact missing object; no inhabitant is asserted. -/
def NativeTorsionLabelAndIndependenceRequired : Prop :=
  Nonempty (NativeTorsionLabelAndIndependenceMissing T)

/-- Recognition: the tTorsionClause produced by the partial gap package uses
the actual torsion carrier. -/
theorem nativeSourceTorsionGapsActual_torsionCarrier
    (torsionLabel : sourceNativeTorsionCarrier (l := l) T → Fin 6)
    (sixTorsionIndependent : Prop)
    (sixTorsionIndependent_proved : sixTorsionIndependent) :
    (nativeSourceTorsionGapsActual T torsionLabel sixTorsionIndependent
      sixTorsionIndependent_proved).toSourceTorsionClause.torsionCarrier =
      sourceNativeTorsionCarrier (l := l) T := rfl

end LeanFormal.IUT.XiFPaper.NativeTorsionGapsSourceFieldsActual

end
