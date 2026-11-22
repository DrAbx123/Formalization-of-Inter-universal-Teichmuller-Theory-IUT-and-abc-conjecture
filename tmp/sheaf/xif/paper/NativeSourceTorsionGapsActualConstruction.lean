import tmp.sheaf.xif.paper.PaperSixTorsionCarrierActual
import tmp.sheaf.n8.closure.NativeSourceTorsionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual NativeSourceTorsionGaps from the six-slot label and clause C

The corrected native torsion carrier is rootsOfUnity 6 in the algebraic closure
of A.F. The actual six-slot label is paperSixTorsionLabel.

The two remaining source conditions are instantiated by actual clause-(c)
facts:

* sixTorsionIndependent := PuncturedEllipticCurve.Torsion23Rational A.curve,
  proved by D.torsion23_rational;
* lTorsionCompatible := Nonempty (rank-two l-torsion basis),
  proved by D.torsion_basis.

No constant label, toy proposition, or arbitrary proof is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeSourceTorsionGapsActualConstruction

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceTorsion
open LeanFormal.IUT.XiFPaper.PaperSixTorsionCarrierActual

universe u

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}
variable (D : SourceClauseC A S C B)

/-- Actual label data for the corrected carrier. -/
noncomputable def nativeSixTorsionLabel (T : SourceNativeInitialThetaData.{0} l) :
    nativeTorsionCarrier (A := T.arithmetic) (l := l) → Fin 6 :=
  paperSixTorsionLabel (T := T)

/-- The actual NativeSourceTorsionGaps record with the six-slot label. -/
noncomputable def nativeSourceTorsionGapsActual
    (T : SourceNativeInitialThetaData.{0} l)
    (D : SourceClauseC T.arithmetic T.tuple.source T.clauseA T.clauseB) :
    NativeSourceTorsionGaps D where
  torsionLabel := nativeSixTorsionLabel (l := l) T
  sixTorsionIndependent :=
    PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve
  sixTorsionIndependent_proved := D.torsion23_rational
  lTorsionCompatible :=
    Nonempty ((Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      T.arithmetic.curve.LTorsion l)
  lTorsionCompatible_proved := ⟨D.torsion_basis⟩

/-- The actual torsion label is the six-slot roots-of-unity label. -/
theorem nativeSourceTorsionGapsActual_torsionLabel
    (T : SourceNativeInitialThetaData.{0} l)
    (D : SourceClauseC T.arithmetic T.tuple.source T.clauseA T.clauseB) :
    (nativeSourceTorsionGapsActual (l := l) T D).torsionLabel =
      nativeSixTorsionLabel (l := l) T := rfl

/-- The actual independence field is clause-(c) six-torsion rationality. -/
theorem nativeSourceTorsionGapsActual_sixTorsionIndependent
    (T : SourceNativeInitialThetaData.{0} l)
    (D : SourceClauseC T.arithmetic T.tuple.source T.clauseA T.clauseB) :
    (nativeSourceTorsionGapsActual (l := l) T D).sixTorsionIndependent =
      PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve := rfl

/-- The actual l-compatibility field is the rank-two l-torsion basis. -/
theorem nativeSourceTorsionGapsActual_lTorsionCompatible
    (T : SourceNativeInitialThetaData.{0} l)
    (D : SourceClauseC T.arithmetic T.tuple.source T.clauseA T.clauseB) :
    (nativeSourceTorsionGapsActual (l := l) T D).lTorsionCompatible =
      Nonempty ((Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
        T.arithmetic.curve.LTorsion l) := rfl

end LeanFormal.IUT.XiFPaper.NativeSourceTorsionGapsActualConstruction

end
