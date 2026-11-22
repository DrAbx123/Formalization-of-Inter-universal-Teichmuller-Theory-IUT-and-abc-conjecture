/- A3 / F2.3: the Fermat chart ring `R n` over ℚ is a domain (needed for the function-field
   and fraction-ring bridge).

  Idea: base change to the algebraic closure is a domain (`chartKbar_isDomain`, DONE 18:11:22)
  and `R n → R n ⊗[ℚ] K` is injective by flatness of `R n` over ℚ (`includeLeft_injective`);
  `IsDomain` pulls back along injective ring maps (`Function.Injective.isDomain`).
  This is the F2.3 prerequisite listed in coord/EXPLICIT-PARAM-AUDIT-GRACE.md §F.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1ChartKbarActual
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.Tactic

noncomputable section
open Polynomial
open scoped TensorProduct
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartFracActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ChartKbarActual

variable (n : Nat)

/-- **chart-0 环 `R n` 是整环**（ℚ 上）。 -/
theorem chartRing_isDomain (hn : 0 < n) : IsDomain (R n) := by
  haveI : IsDomain (R n ⊗[ℚ] K) := chartKbar_isDomain n hn
  haveI : Module.Flat ℚ (R n) := Module.Flat.of_free
  have hb : Function.Injective (algebraMap ℚ K) :=
    FaithfulSMul.algebraMap_injective ℚ K
  have hAlg : Function.Injective
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (A := R n) (B := K)) := by
    exact Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := R n) (B := K) hb
  let f : R n →+* (R n ⊗[ℚ] K) :=
    (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (A := R n) (B := K)).toRingHom
  have hf : Function.Injective f := by
    intro a b h
    exact hAlg (by simpa [f] using h)
  exact Function.Injective.isDomain f hf

#print axioms chartRing_isDomain
