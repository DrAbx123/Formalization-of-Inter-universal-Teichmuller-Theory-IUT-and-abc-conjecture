import tmp.sheaf.n8.closure.EtaHaarCharNormIdentification
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.EtaHaarCharNormIdentification
open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Pointwise
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
  {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
#check (Integers K).subtype
noncomputable def integerUnitInK (u : (Integers K)ˣ) : Kˣ :=
  Units.map (Integers K).subtype.toMonoidHom u
#check integerUnitInK
