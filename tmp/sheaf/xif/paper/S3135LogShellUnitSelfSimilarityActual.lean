import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellScalarClosure

/-!
# task-54 (2): integral-log-shell self-similarity under integral units

**COMPONENT, not a paper object.**  Consumer: F4 (b2) `integralLogShell`
self-similarity under the paper scaling `lambda` (log-degree 0 = unit).

If `u` is a unit of the actual integers `Integers K` of the normalized completion, then
both `u` and `u^{-1}` are `p`-adic integral scalars, so by the actual lattice closure
lemma `integralLogShell_padicInt_mul_mem` multiplication by `u` maps the integral
log-shell into itself bijectively:

`(fun x => (u : K) * x) '' integralLogShell = integralLogShell`.

This is the log-shell self-similarity of the unit-scaling normalization
(IUT III Proposition 3.9(i) p.115; Remark 3.9.5(i)): the paper `lambda` with
log-degree 0 is a unit of the integral structure, hence preserves the actual lattice.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual

namespace LeanFormal.IUT.XiFPaper.S3135LogShellUnitSelfSimilarityActual

/-- **Integral-unit self-similarity of the actual integral log-shell.** -/
theorem s3135_integralLogShell_unit_selfSimilarity
    (u : (Integers (K := concreteLogShellField))ˣ) :
    (fun x => ((u : Integers (K := concreteLogShellField)) :
        concreteLogShellField) * x) '' ((integralLogShell
          (K := concreteLogShellField) (p := concreteRationalPrime)) :
            Set concreteLogShellField) =
      ((integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)) : Set concreteLogShellField) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact integralLogShell_padicInt_mul_mem
      (K := concreteLogShellField) (p := concreteRationalPrime)
      (u : Integers (K := concreteLogShellField)) hy
  · intro hx
    refine ⟨(((u⁻¹ : (Integers (K := concreteLogShellField))ˣ) :
        Integers (K := concreteLogShellField)) : concreteLogShellField) * x, ?_, ?_⟩
    · exact integralLogShell_padicInt_mul_mem
        (K := concreteLogShellField) (p := concreteRationalPrime)
        ((u⁻¹ : (Integers (K := concreteLogShellField))ˣ) :
          Integers (K := concreteLogShellField)) hx
    · rw [← mul_assoc]
      simp

#check s3135_integralLogShell_unit_selfSimilarity

end LeanFormal.IUT.XiFPaper.S3135LogShellUnitSelfSimilarityActual
end
