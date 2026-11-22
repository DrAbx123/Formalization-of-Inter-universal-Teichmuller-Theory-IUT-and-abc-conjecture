import tmp.sheaf.xif.paper.Mzk1P7SourceHlineActual
import tmp.sheaf.xif.paper.Mzk1P7TransvectionLargeImageActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7DLargeImageActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1P7SourceHlineActual
open LeanFormal.IUT.XiFPaper.Mzk1P7TransvectionLargeImageActual
open Matrix
variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}
/-- P7 D-indexed large-image instance: a transvection in the D-indexed
mod-l image plus the D-indexed no-invariant-line condition gives full SL2. -/
theorem p7_D_largeImage_of_transvection
    (D : SourceClauseC A S C B)
    (hT : ∃ T : GL (Fin 2) (ZMod l.value),
      T ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range ∧
      T ≠ 1 ∧
      ((T : Matrix (Fin 2) (Fin 2) (ZMod l.value)) - 1) ^ 2 = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) :
    g.toGL ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range :=
  p7_sl2_le_range_of_transvection (A.curve) D.torsion_basis hT
    (p7_source_no_invariant_line D) g
#print axioms p7_D_largeImage_of_transvection
end LeanFormal.IUT.XiFPaper.Mzk1P7DLargeImageActual
end