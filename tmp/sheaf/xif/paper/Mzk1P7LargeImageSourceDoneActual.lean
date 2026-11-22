import tmp.sheaf.xif.paper.Mzk1P7SourceTransvectionActual
import tmp.sheaf.xif.paper.Mzk1P7SourceHlineActual
import tmp.sheaf.xif.paper.Mzk1P7TransvectionLargeImageActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageSourceDoneActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open Matrix

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}

/-- General D-indexed large-image step: a transvection and no-invariant-line
data in the canonical representation yield the full `SL₂` image. -/
theorem p7_D_largeImage_of_transvection (D : SourceClauseC A S C B)
    (hT : ∃ T : GL (Fin 2) (ZMod l.value),
      T ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range ∧
      T ≠ 1 ∧
      ((T : Matrix (Fin 2) (Fin 2) (ZMod l.value)) - 1) ^ 2 = 0)
    (hline : ∀ v : Fin 2 → ZMod l.value, v ≠ 0 →
      ∃ g ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range,
        ∀ c : ZMod l.value,
          Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (ZMod l.value)) v ≠ c • v)
    (M : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) :
    M.toGL ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range :=
  LeanFormal.IUT.XiFPaper.Mzk1P7TransvectionLargeImageActual.p7_sl2_le_range_of_transvection
    A.curve D.torsion_basis hT hline M

/-- Actual large-image source: `SL₂(𝔽_l)` lies in the canonical mod-`l`
representation range, using the actual source transvection and no-line data. -/
theorem p7_D_largeImage_source (D : SourceClauseC A S C B) :
    ∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value),
      M.toGL ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range :=
  fun M => p7_D_largeImage_of_transvection D
    (LeanFormal.IUT.XiFPaper.Mzk1P7SourceTransvectionActual.p7_source_transvection_data D)
    (LeanFormal.IUT.XiFPaper.Mzk1P7SourceHlineActual.p7_source_no_invariant_line D) M

#print axioms p7_D_largeImage_of_transvection
#print axioms p7_D_largeImage_source
end LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageSourceDoneActual