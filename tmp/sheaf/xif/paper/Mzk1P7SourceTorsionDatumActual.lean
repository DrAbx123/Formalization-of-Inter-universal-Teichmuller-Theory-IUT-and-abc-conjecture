/- P7 actual frozen torsion datum from a native input: torsion basis, large
image and kernel-field identification are read from the native clause-(c)
record, and the actual SourceClauseC is reconstructed from that datum. -/
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.xif.paper.Mzk1P7SourceClauseActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7SourceTorsionDatumActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1P7SourceClauseActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual frozen torsion datum attached to a native input: all three fields
are read from the native clause-(c) record. -/
noncomputable def sourceTorsionDatumOfNative :
    SourceTorsionDatum l X.S.arithmetic where
  torsion_basis := X.S.clauseC.torsion_basis
  image_contains_SL2 := by
    have h := X.S.clauseC.image_contains_SL2
    rwa [X.S.clauseC.representation_eq_canonical] at h
  kernel_field_identification := X.S.clauseC.kernel_field_identification

/-- Actual SourceClauseC reconstructed from the native torsion datum and the
native 2/3-torsion rationality. -/
noncomputable def sourceClauseC_of_native :
    SourceClauseC X.S.arithmetic X.S.tuple.source X.S.clauseA X.S.clauseB :=
  sourceClauseC_of_torsionDatum (S := X.S.tuple.source) (C := X.S.clauseA)
    (B := X.S.clauseB) (sourceTorsionDatumOfNative X)
    X.S.clauseC.torsion23_rational

#print axioms sourceTorsionDatumOfNative
#print axioms sourceClauseC_of_native

end LeanFormal.IUT.XiFPaper.Mzk1P7SourceTorsionDatumActual
end
