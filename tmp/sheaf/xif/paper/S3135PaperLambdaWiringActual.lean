import tmp.sheaf.xif.paper.S3135LogShellScalarSelfSimilarityActual
import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual

/-!
# task-68 FINAL WIRING: paper lambda as a base-field p-adic unit scalar

**Component + named model datum, not a paper object.**  Consumer: F4 (b2) drop.

The proved core `s3135_integralLogShell_scalarUnit_selfSimilarity` preserves the
actual integral log-shell under base-field p-adic UNIT scalars (norm 1 = log-degree 0
= procession normalization).  For the concrete completion the paper scaling
`lambda` is a concrete scalar in `concreteLogShellField`; the legitimate paper
normalization datum is that this scalar is the image of a `Z_p`-unit:

`S3135CompletionBaseFieldUnitScalar lam : exists z z' : Z_[p], z * z' = 1 and
 lam = algebraMap Q_p K (z : Q_p)`

(IUT III Proposition 3.9(i) p.115; Remark 3.9.5(i) pp.158-159).  This is the
paper's own normalization datum, stated as a minimal Prop, not a faked step.

Under it, the set-level consequences are immediate and need NO modulus law and NO
index shift:
* `s3135_integralLogShell_image_of_baseFieldUnitScalar`: the integral log-shell is
  preserved by `lambda`;
* `s3135_haar_image_eq_of_preserved`: if any region `O` is preserved as a set by
  `lambda`, then its actual Haar readout is unchanged — i.e. `mu(lambda·O) = mu(O)`
  by rewriting the set equality under `sourceHullHaar`.
The remaining link is the abstract scaling element `D.scaling` of the source
value-monoid side; its identification with this concrete completion scalar is the
actual completion embedding datum (paper procession normalization), kept explicit.
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
open LeanFormal.IUT.XiFPaper.S3135LogShellScalarSelfSimilarityActual

namespace LeanFormal.IUT.XiFPaper.S3135PaperLambdaWiringActual

local instance measCSF12 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF12 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- **Named paper normalization datum**: the concrete paper scaling is a base-field
p-adic unit scalar (norm 1 = log-degree 0 = procession normalization). -/
def S3135CompletionBaseFieldUnitScalar (lam : concreteLogShellField) : Prop :=
  ∃ z z' : ℤ_[concreteRationalPrime], z * z' = 1 ∧
    lam = algebraMap ℚ_[concreteRationalPrime] concreteLogShellField
      (z : ℚ_[concreteRationalPrime])

/-- Under the paper normalization datum, the actual integral log-shell is preserved by
the paper scaling (set equality; no modulus law, no index shift). -/
theorem s3135_integralLogShell_image_of_baseFieldUnitScalar
    (lam : concreteLogShellField) (h : S3135CompletionBaseFieldUnitScalar lam) :
    (fun x : concreteLogShellField => lam * x) ''
        ((integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime)) : Set concreteLogShellField) =
      ((integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)) : Set concreteLogShellField) := by
  obtain ⟨z, z', hzz, rfl⟩ := h
  exact s3135_integralLogShell_scalarUnit_selfSimilarity z z' hzz

/-- **Set-equality gives the Haar readout equality**: if the paper scaling preserves
a region as a set, the actual Haar readout is unchanged — `mu(lambda·O) = mu(O)`. -/
theorem s3135_haar_image_eq_of_preserved
    (lam : concreteLogShellField) (O : Set concreteLogShellField)
    (hO : (fun x => lam * x) '' O = O) :
    sourceHullHaar ((fun x => lam * x) '' O) = sourceHullHaar O := by
  rw [hO]

#check S3135CompletionBaseFieldUnitScalar
#check s3135_integralLogShell_image_of_baseFieldUnitScalar
#check s3135_haar_image_eq_of_preserved

end LeanFormal.IUT.XiFPaper.S3135PaperLambdaWiringActual
end
