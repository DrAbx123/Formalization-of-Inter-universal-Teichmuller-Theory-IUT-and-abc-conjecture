/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.RingTheory.Norm.Transitivity
import LeanFormal.IUT.ABCBridge.Geometry.RelativeCompletionFinrankReduction

/-!
# P5-D: C13 Galois norm invariance + C18 completion restriction-of-scalars

Status: PARTIAL/green-target probes for P5-D.

* C13: for a finite Galois extension `L/K`, the Galois invariance form of the norm
  `algebraMap K L (Algebra.norm K x) = ∏ σ : Gal(L/K), σ x`, and its fixed-field
  invariance.
* C18: the actual relative-completion norm transport at a finite place,
  `||algebraMap k K a||_w = ||a||_v ^ [K_w : k_v]`, instantiated from
  `RelativeCompletionFinrankReduction.norm_algebraMap_pow_of_finrank_eq_relativeCompletionDegree`.

No new structure fields, no target assumptions, no sorry/axiom.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P5DCNormGaloisCompletionActual

open scoped Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

section GaloisNorm

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- C13: the Galois product formula for the norm. -/
theorem c13_algebraMap_norm_eq_prod_automorphisms (x : L) :
    algebraMap K L (Algebra.norm K x) = ∏ σ : Gal(L/K), σ x :=
  Algebra.norm_eq_prod_automorphisms (K := K) (L := L) x

/-- C13 fixed-field consequence: the norm is fixed by every Galois automorphism. -/
theorem c13_norm_galois_invariant (x : L) (σ : Gal(L/K)) :
    σ (algebraMap K L (Algebra.norm K x)) = algebraMap K L (Algebra.norm K x) :=
  σ.commutes (Algebra.norm K x)

end GaloisNorm

section CompletionNorm

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- C18: actual relative-completion norm transport on the image of a base element. -/
theorem c18_norm_algebraMap_completion_eq_pow
    (place : NumberField.FinitePlace K) (a : k) (ha : a ≠ 0) :
    ‖(algebraMap k K a : place.maximalIdeal.adicCompletion K)‖ =
      ‖(a : (comap (k := k) place).maximalIdeal.adicCompletion k)‖ ^
        Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
          (place.maximalIdeal.adicCompletion K) :=
  norm_algebraMap_pow_of_finrank_eq_relativeCompletionDegree
    (k := k) place a ha

/-- C18 in signed-log form, the convention consumed by the q-pilot normalization chain. -/
theorem c18_logNorm_algebraMap_completion_eq_mul
    (place : NumberField.FinitePlace K) (a : k) (ha : a ≠ 0) :
    Real.log ‖(algebraMap k K a : place.maximalIdeal.adicCompletion K)‖ =
      (Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) : ℝ) *
        Real.log ‖(a : (comap (k := k) place).maximalIdeal.adicCompletion k)‖ :=
  logNorm_algebraMap_eq_mul_of_finrank_eq_relativeCompletionDegree
    (k := k) place a ha

end CompletionNorm

def p5dRows : List (String × String × String) :=
  [ ("c13_algebraMap_norm_eq_prod_automorphisms", "Galois norm product formula", "PROVED (Mathlib)"),
    ("c13_norm_galois_invariant", "Galois fixed-field invariance", "PROVED"),
    ("c18_norm_algebraMap_completion_eq_pow", "actual completion norm transport", "PROVED (instantiation)"),
    ("c18_logNorm_algebraMap_completion_eq_mul", "log form", "PROVED (instantiation)") ]

theorem p5dRows_length : p5dRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P5DCNormGaloisCompletionActual
