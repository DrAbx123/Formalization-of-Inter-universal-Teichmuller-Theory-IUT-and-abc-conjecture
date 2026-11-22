/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DegreeSumActual
import Mathlib.Tactic

/-! # GAP-NORM-ARCH: arch-normalized Arakelov degree -/

/-
| field | value |
|---|---|
| Status | green attempt: arch normalization factor `c` entering the Example36 explicit-divisor degree; product-formula consequence for principal divisors |
| Reuse | `Mzk1DegreeSumActual`（`globalPrimeStripWeight`, `nativeBadQAbsLogSum`, task-99/105）; `Example36ProductFormula:313/387` |
| GAP | GAP-NORM-ARCH: paper arch normalization (`1/[K:Q]`, `1/(2ℓ)` on the q side) not yet identified with `c`; only the abstract factor is treated |
| 纪律 | no sorry/axiom; no new assumptions |
-/

noncomputable section
open scoped BigOperators NumberField
open IsDedekindDomain NumberField

namespace LeanFormal.IUT.XiFPaper.Mzk1NormArchDegreeActual

open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PrimeStripProductFormula
open LeanFormal.IUT.XiFPaper.Mzk1DegreeSumActual

variable {F : Type*} [Field F] [NumberField F]

/-- Arch-normalized explicit-divisor degree: finite part unchanged, archimedean part
multiplied by the normalization factor `c` (`c = 1` is the unnormalized Example36 degree). -/
noncomputable def archNormalizedDegree
    (c : ℝ) (d : SourceModelBackend.ExplicitDivisor F) : ℝ :=
  d.1.sum (fun v n =>
      (n : ℝ) * Real.log (finitePlaceResidueCardinality (F := F) v))
    + c * (∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) * d.2 w)

/-- `c = 1` recovers the unnormalized Example36 degree. -/
theorem archNormalizedDegree_one
    (d : SourceModelBackend.ExplicitDivisor F) :
    archNormalizedDegree 1 d = globalPrimeStripWeight (F := F) d := by
  unfold archNormalizedDegree globalPrimeStripWeight
  ring

/-- **Product-formula consequence**: if the unnormalized degree vanishes (e.g. a principal
divisor), the arch-normalized degree is `(c - 1)` times the archimedean sum. -/
theorem archNormalizedDegree_of_degree_zero
    (c : ℝ) (d : SourceModelBackend.ExplicitDivisor F)
    (h : globalPrimeStripWeight (F := F) d = 0) :
    archNormalizedDegree c d =
      (c - 1) * (∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) * d.2 w) := by
  unfold archNormalizedDegree globalPrimeStripWeight at *
  linarith

/-- **Principal-unit form**: for the explicit principal divisor of a global unit, the
arch-normalized degree is `(c - 1)` times the archimedean sum. -/
theorem archNormalizedDegree_principalUnit
    (c : ℝ) (f : Fˣ) :
    archNormalizedDegree c
      (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) =
      (c - 1) * (∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) *
          (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)).2 w) :=
  archNormalizedDegree_of_degree_zero c _
    (globalPrimeStripWeight_principalDivisorExplicit (F := F) f)

def normArchRows : List (String × String) :=
  [ ("archNormalizedDegree", "arch factor c on the Example36 explicit-divisor degree") ,
    ("archNormalizedDegree_one", "c=1 recovers globalPrimeStripWeight (PROVED)") ,
    ("archNormalizedDegree_of_degree_zero", "zero-degree case: (c-1)*arch (PROVED)") ,
    ("archNormalizedDegree_principalUnit", "principal unit form (PROVED)") ,
    ("GAP-NORM-ARCH", "paper 1/[K:Q] / 1/(2l) identification with c still open") ]

theorem normArchRows_length : normArchRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1NormArchDegreeActual