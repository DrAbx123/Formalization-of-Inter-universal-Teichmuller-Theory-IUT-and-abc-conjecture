import tmp.sheaf.xif.paper.S1962R1AbstractActionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace Probe

#check @LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual.R1JointContinuousActionMissing
#check @sourceUnitPerfectionIndTopology
#check @sourceUnitPerfectionIndHomeomorph
#check @sourceAlgebraicFieldIndTopology
#check @LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual.PsiTildeGroup
#check @LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual.PsiTilde

-- topology on the Galois group?
variable {K : Type*} [Field K] [NumberField K] (place : NumberField.FinitePlace K)
#synth TopologicalSpace (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place] SourceAlgebraicClosure place)
#synth TopologicalGroup (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place] SourceAlgebraicClosure place)
#synth CompactSpace (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place] SourceAlgebraicClosure place)
#synth NontriviallyNormedField (SourceAlgebraicClosure place)
#synth IsUltrametricDist (SourceAlgebraicClosure place)

end Probe
