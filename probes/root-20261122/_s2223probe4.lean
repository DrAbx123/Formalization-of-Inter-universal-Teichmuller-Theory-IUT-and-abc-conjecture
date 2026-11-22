
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2190RootSourceConditionsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual

namespace S2223Probe

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev LF (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=
  AlgebraicClosure T.arithmetic.F
abbrev LK (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=
  AlgebraicClosure (Kv T b)

noncomputable def kAlgHomLF : T.arithmetic.K →ₐ[T.arithmetic.F] LF T b :=
  (IntermediateField.val (T.arithmetic.curve.galoisLTorsionKernelField l T.clauseC.torsion_basis)).comp
    T.clauseC.kernel_field_identification.toAlgHom

example : Algebra T.arithmetic.K (LF T b) := (kAlgHomLF T b).toRingHom.toAlgebra
example : Algebra T.arithmetic.K (LK T b) := inferInstance
example : IsScalarTower T.arithmetic.F T.arithmetic.K (LK T b) := inferInstance
example : Algebra.IsAlgebraic T.arithmetic.K (LK T b) := by
  exact Algebra.IsAlgebraic.trans (R := T.arithmetic.K) (S := Kv T b) (A := LK T b)

end S2223Probe
end
