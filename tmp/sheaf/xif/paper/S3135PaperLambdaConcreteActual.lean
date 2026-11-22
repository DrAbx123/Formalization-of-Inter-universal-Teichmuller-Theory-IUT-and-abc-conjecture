import tmp.sheaf.xif.paper.S3135PaperLambdaWiringActual

/-!
# task-68 route (B) result: the concrete normalized model REALIZES the paper scaling as a Z_p-unit

**Citable route-B finding, not a paper object.**  Route (B) (search for the actual
identification before any datum) inspected the source of the scaling field:

* the actual concrete Haar model `SourceUnitRegionHaarDataActual.lean:421` sets
  `scaling := 1` (the concrete normalized model's scaling is the trivial unit);
* the actual Example36 shells use the concrete base-field scalar
  `(logShellScale concreteRationalPrime : K)⁻¹` in the scaled unit-log image
  (`Example36LogKummerMap.lean:281-282`), so all recorded concrete scalars are
  actual base-field elements.

Consequently, for the concrete normalized model the paper normalization datum is
proved, not assumed:

`s3135_concrete_scaling_unitScalar : S3135CompletionBaseFieldUnitScalar (1 : K)`
(with `z = z' = 1`), and hence `mu(lambda·O) = mu(O)` for the standard (trivial)
scaling by the set-equality corollary: `s3135_concrete_haar_image_eq`.

For an ARBITRARY abstract `D : I.SourceUnitRegionHaarData v R n` the frozen source
model records only a value-group scaling element (`scaling` field of the abstract
record; the carrier fields give only `logDegree <= 0`), with no concrete completion
scalar recorded.  So for the general gate the single flagged input of F4 (b) is the
paper normalization datum `S3135CompletionBaseFieldUnitScalar` (already stated as a
minimal Prop), justified as the paper's own procession-normalization input
(IUT III Proposition 3.9(i) p.115; Remark 3.9.5(i) pp.158-159) — NOT a surrogate.
-/

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Measure
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3135PaperLambdaWiringActual

namespace LeanFormal.IUT.XiFPaper.S3135PaperLambdaConcreteActual

local instance measCSF13 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF13 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- **Route (B) landed for the concrete normalized model**: the standard scaling
`1` is an actual base-field p-adic unit scalar. -/
theorem s3135_concrete_scaling_unitScalar :
    S3135CompletionBaseFieldUnitScalar (1 : concreteLogShellField) := by
  refine ⟨1, 1, by simp, ?_⟩
  simp

/-- Hence `mu(lambda·O) = mu(O)` for the concrete normalized scaling by set equality
(no modulus law, no index shift). -/
theorem s3135_concrete_haar_image_eq (O : Set concreteLogShellField) :
    sourceHullHaar ((fun x : concreteLogShellField => (1 : concreteLogShellField) * x) '' O) =
      sourceHullHaar O := by
  rw [s3135_haar_image_eq_of_preserved (1 : concreteLogShellField) O (by simp)]

#check s3135_concrete_scaling_unitScalar
#check s3135_concrete_haar_image_eq

end LeanFormal.IUT.XiFPaper.S3135PaperLambdaConcreteActual
end
