import tmp.sheaf.xif.paper.Mzk1S3137ThetaBlockFactorNonposActual
import tmp.sheaf.xif.paper.Mzk1C3BlockMeasureActual
import tmp.sheaf.xif.paper.PrimeStripLogShellActual

/-! P7 #7 THETA-DEG: [C3 block:Q_p] vs local degree (CONDITIONAL/PARTIAL).

The block dimension is the product of the local degrees
`[CommonPrimeCompletion place : Q_p] = Module.finrank`; block log-p factor
nonpositivity is already green. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaBlockFactorNonposActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaRawEqActual
open LeanFormal.IUT.XiFPaper.Mzk1C3BlockMeasureActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual

variable {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]

/-- Local degree `[K_v : Q_p]` as the Q_p-dimension of the actual completion. -/
def localCompletionDegree (place : FinitePlaceAtPrime K p) : Nat :=
  Module.finrank ℚ_[p] (CommonPrimeCompletion place)

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The C3 tensor block dimension is the product of the actual local degrees. -/
theorem c3TensorBlockDimension_eq_prod_localCompletionDegree :
    c3TensorBlockDimension C3 =
      ∏ i : C3.tensorIndex, localCompletionDegree (c3LogShellPlace C3 i) := by
  letI : Fact (Nat.Prime C3.p) := C3.hp
  rw [c3TensorBlockDimension_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  rfl

/-- #7 conditional identification: nonpositive block factor + local-degree factorization. -/
theorem thetaDeg_block_nonpos_and_localDegree :
    thetaBlockLogFactor C3 ≤ 0 ∧
      c3TensorBlockDimension C3 =
        ∏ i : C3.tensorIndex, localCompletionDegree (c3LogShellPlace C3 i) :=
  ⟨thetaBlockLogFactor_nonpos C3,
    c3TensorBlockDimension_eq_prod_localCompletionDegree C3⟩

end LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegActual
end