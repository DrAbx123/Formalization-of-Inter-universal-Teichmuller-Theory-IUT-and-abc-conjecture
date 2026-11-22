/- A3 / F2.3: the remaining chart rings (at infinity and the overlap) are domains over ℚ.

  Same method as `Mzk1G1A3ChartFracActual.chartRing_isDomain`: base change to the algebraic
  closure K is a domain (`chartKbarInf_isDomain` 18:24:33, `overlapKbar_isDomain` 19:44:32)
  and `A → A ⊗[ℚ] K` is injective by flatness (`Algebra.TensorProduct.includeLeft_injective`),
  so `IsDomain` pulls back along the injective ring map (`Function.Injective.isDomain`).
  These supply `IsIntegral (Spec ...)` for the two charts and the overlap, the input of the
  generic `Scheme.GlueData.glued_isIntegral` for `IsIntegral (fermatCurveScheme n)` (next batch).
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatChartInfKbarActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapKbarActual
import tmp.sheaf.xif.paper.Mzk1G1A3ChartFracActual
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.Tactic

noncomputable section
open Polynomial
open scoped TensorProduct
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveDomainActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartInfKbarActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ChartKbarActual

variable (n : Nat)

/-- **无穷远 chart 环 `R2 n` 是整环**（ℚ 上）。 -/
theorem chartInfRing_isDomain (hn : 0 < n) : IsDomain (R2 n) := by
  haveI : IsDomain (R2 n ⊗[ℚ] K) := chartKbarInf_isDomain n hn
  haveI : Module.Flat ℚ (R2 n) := Module.Flat.of_free
  have hb : Function.Injective (algebraMap ℚ K) :=
    FaithfulSMul.algebraMap_injective ℚ K
  have hAlg : Function.Injective
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (A := R2 n) (B := K)) := by
    exact Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := R2 n) (B := K) hb
  let f : R2 n →+* (R2 n ⊗[ℚ] K) :=
    (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (A := R2 n) (B := K)).toRingHom
  have hf : Function.Injective f := by
    intro a b h
    exact hAlg (by simpa [f] using h)
  exact Function.Injective.isDomain f hf

/-- **overlap 环 `Overlap0 n` 是整环**（ℚ 上）。 -/
theorem overlapRing_isDomain (hn : 0 < n) : IsDomain (Overlap0 n) := by
  haveI : IsDomain (Overlap0 n ⊗[ℚ] K) :=
    LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapKbarActual.overlapKbar_isDomain n hn
  haveI : Module.Flat ℚ (Overlap0 n) := Module.Flat.of_free
  have hb : Function.Injective (algebraMap ℚ K) :=
    FaithfulSMul.algebraMap_injective ℚ K
  have hAlg : Function.Injective
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (A := Overlap0 n) (B := K)) := by
    exact Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := Overlap0 n) (B := K) hb
  let f : Overlap0 n →+* (Overlap0 n ⊗[ℚ] K) :=
    (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (A := Overlap0 n) (B := K)).toRingHom
  have hf : Function.Injective f := by
    intro a b h
    exact hAlg (by simpa [f] using h)
  exact Function.Injective.isDomain f hf

#print axioms chartInfRing_isDomain
#print axioms overlapRing_isDomain

end LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveDomainActual