/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormArchDegreeActual
import tmp.sheaf.xif.paper.S3050StepVQExpansionActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import Mathlib.Tactic

/-! # GAP-NORM-ARCH: paper normalization factors vs archNormalizedDegree `c` -/

/-
| field | value |
|---|---|
| Status | PARTIAL/green: paper c_root factor `1/(2l)` identified with `S3050Unit` coefficient; `paperArchFactor l = 1/(2l)` and its arch-normalized degree formula; `T(l)` re-export; `1/[K:Q]` and `c` identification are precise GAPs |
| Reuse | `S3050StepVQExpansionActual:18-20 S3050Unit`（= `(order/(2l))·log p`）; `Mzk1PrimeConductorRouteActual:58 T`; `Mzk1NormArchDegreeActual` |
| GAP | GAP-NORM-ARCH-C: paper arch normalization factor (`1/[K:Q]`, and whether it equals `1/(2l)`) is not identified with `c`; `T(l)` is the abc Route-C threshold, not the arch factor |
| 纪律 | no sorry/axiom; no new assumptions |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NormFactorDictionaryActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PrimeStripProductFormula
open LeanFormal.IUT.XiFPaper.Mzk1NormArchDegreeActual
open LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

/-- Paper c_root coefficient `order/(2l)` (the coefficient of `log p`). -/
noncomputable def paperCRoot (order : ℝ) (l : ℕ) : ℝ :=
  order / (2 * (l : ℝ))

/-- `S3050Unit` is exactly the paper c_root coefficient times `log p`. -/
theorem S3050Unit_eq_paperCRoot_mul_logp
    {K : Type*} [Norm K] (p : ℕ) (jValue : K) (l : ℕ) :
    S3050Unit p jValue l =
      paperCRoot (localNormOrder p jValue) l * Real.log (p : ℝ) := by
  unfold S3050Unit paperCRoot
  push_cast
  ring

/-- The paper arch normalization factor `1/(2l)` used on the q side. -/
noncomputable def paperArchFactor (l : ℕ) : ℝ :=
  1 / (2 * (l : ℝ))

/-- Arch-normalized degree with the paper factor `c = 1/(2l)` (template). -/
theorem archNormalizedDegree_paperArchFactor
    {F : Type*} [Field F] [NumberField F]
    (l : ℕ) (d : SourceModelBackend.ExplicitDivisor F) :
    archNormalizedDegree (paperArchFactor l) d =
      d.1.sum (fun v n =>
          (n : ℝ) * Real.log (finitePlaceResidueCardinality (F := F) v))
        + paperArchFactor l * (∑ w : NumberField.InfinitePlace F,
            (NumberField.InfinitePlace.mult w : ℝ) * d.2 w) :=
  rfl

/-- Principal-unit consequence with the paper arch factor. -/
theorem archNormalizedDegree_paperArchFactor_principalUnit
    {F : Type*} [Field F] [NumberField F]
    (l : ℕ) (f : Fˣ) :
    archNormalizedDegree (paperArchFactor l)
      (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) =
      (paperArchFactor l - 1) * (∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) *
          (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)).2 w) :=
  archNormalizedDegree_principalUnit (paperArchFactor l) f

/-- Route-C threshold `T(l)` (re-export), recorded for the normalization dictionary. -/
theorem T_eq_routeC (l : ℝ) :
    T l = 6 * l * (l + 5) / ((l + 4) * (l - 3)) := rfl

def normFactorRows : List (String × String) :=
  [ ("paperCRoot", "paper c_root coefficient order/(2l)") ,
    ("S3050Unit_eq_paperCRoot_mul_logp", "S3050Unit = paperCRoot * log p (PROVED)") ,
    ("paperArchFactor", "paper arch factor 1/(2l)") ,
    ("archNormalizedDegree_paperArchFactor", "c=1/(2l) template (rfl)") ,
    ("archNormalizedDegree_paperArchFactor_principalUnit", "principal unit c=1/(2l) (PROVED)") ,
    ("T_eq_routeC", "T(l) re-export (rfl)") ,
    ("GAP-NORM-ARCH-C", "1/[K:Q] and c identification with paper arch factor are not constructed") ]

theorem normFactorRows_length : normFactorRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1NormFactorDictionaryActual