import tmp.sheaf.xif.paper.Mzk1P7LargeImageSourceDoneActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCSupportActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open Matrix
variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}
/-- P7 Clause C support: the actual D-indexed transvection, no-line, and
large-image data attached to a `SourceClauseC`. -/
structure P7ClauseCSupport (D : SourceClauseC A S C B) : Prop where
  transvection :
    ∃ T : GL (Fin 2) (ZMod l.value),
      T ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range ∧
      T ≠ 1 ∧
      ((T : Matrix (Fin 2) (Fin 2) (ZMod l.value)) - 1) ^ 2 = 0
  no_invariant_line :
    ∀ v : Fin 2 → ZMod l.value, v ≠ 0 →
      ∃ g ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range,
        ∀ c : ZMod l.value,
          (g : Matrix (Fin 2) (Fin 2) (ZMod l.value)) *ᵥ v ≠ c • v
  large_image :
    ∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value),
      M.toGL ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range
/-- Actual Clause C support, built from the source transvection, source
no-invariant-line, and D-indexed large-image theorems. -/
theorem p7_clauseC_support (D : SourceClauseC A S C B) :
    P7ClauseCSupport (l := l) D where
  transvection :=
    LeanFormal.IUT.XiFPaper.Mzk1P7SourceTransvectionActual.p7_source_transvection_data D
  no_invariant_line :=
    LeanFormal.IUT.XiFPaper.Mzk1P7SourceHlineActual.p7_source_no_invariant_line D
  large_image :=
    LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageSourceDoneActual.p7_D_largeImage_source D
#print axioms p7_clauseC_support
end LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCSupportActual
end