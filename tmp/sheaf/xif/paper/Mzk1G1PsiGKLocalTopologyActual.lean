/- G-K §7.3 local topology package, batch 1: L_v-point models of the two Fermat charts.

An `L`-point of chart 0 (Spec of `R n`) is a pair (a,b) ∈ L² with `a^n + b^n = 1`;
an `L`-point of the infinity chart is a pair (s,r) with `1 + s^n = r^n`. This file
records the forward maps (ring hom ↦ coordinates) and the defining relations, which are
the basis for the topology and for the compactness argument of route §7.3 (L671-705).
-/
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual

/-- The set of `L`-points of the first (affine) Fermat chart: `a^n + b^n = 1`. -/
def chart0Points (n : Nat) (L : Type) [Field L] [Algebra ℚ L] : Set (L × L) :=
  {p | p.1 ^ n + p.2 ^ n = 1}

/-- The set of `L`-points of the infinity chart: `1 + s^n = r^n`. -/
def chartInfPoints (n : Nat) (L : Type) [Field L] [Algebra ℚ L] : Set (L × L) :=
  {p | 1 + p.1 ^ n = p.2 ^ n}

/-- Coordinates of a ring hom `R n →+* L` (an `L`-point of chart 0). -/
def chart0PointOfHom {L : Type} [Field L] [Algebra ℚ L] (n : Nat) (φ : R n →+* L) : L × L :=
  (φ (x0 n), φ (x1 n))

/-- Coordinates of a ring hom `R2 n →+* L` (an `L`-point of the infinity chart). -/
def chartInfPointOfHom {L : Type} [Field L] [Algebra ℚ L] (n : Nat) (φ : R2 n →+* L) : L × L :=
  (φ (s1 n), φ (r1 n))

/-- The coordinates of a chart-0 `L`-point satisfy the Fermat relation. -/
theorem chart0PointOfHom_mem {L : Type} [Field L] [Algebra ℚ L] (n : Nat)
    (φ : R n →+* L) : chart0PointOfHom n φ ∈ chart0Points n L := by
  have h : x0 n ^ n + x1 n ^ n = 1 := chart0_relation n
  have h' := congrArg φ h
  simpa [chart0Points, chart0PointOfHom] using h'

/-- The coordinates of a chart-infinity `L`-point satisfy the second relation. -/
theorem chartInfPointOfHom_mem {L : Type} [Field L] [Algebra ℚ L] (n : Nat)
    (φ : R2 n →+* L) : chartInfPointOfHom n φ ∈ chartInfPoints n L := by
  have h : 1 + s1 n ^ n = r1 n ^ n := chartInf_relation n
  have h' := congrArg φ h
  simpa [chartInfPoints, chartInfPointOfHom] using h'

#print axioms chart0PointOfHom_mem
#print axioms chartInfPointOfHom_mem
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyActual
