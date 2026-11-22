import LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientChartCoverFromRefinement
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientPieceIdentification
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Affine quotient chart-cover data from the refined quotient cover

The green module QuotientChartCoverFromRefinement produces a finite family of
invariant sections whose basic opens cover Spec(A^G).  This file turns that
cover into the unit-ideal generation statement Ideal.span (Set.range Hq) = top,
using PrimeSpectrum.iSup_basicOpen_eq_top_iff, and then constructs the actual
AffineQuotientChartCoverData via AffineQuotientChartCoverData.ofFamily.
No residual data is assumed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientChartCoverDataFromRefinement

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientChartCoverFromRefinement
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientPieceIdentification

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable {G : Type u} [Group G] [MulSemiringAction G A] [SMulCommClass G R A] [Fintype G]

/-- A finite family of invariant sections whose basic opens cover the spectrum
generates the unit ideal. -/
theorem ideal_span_range_eq_top_of_cover
    {ι : Type u} [Fintype ι]
    (H : ι → FixedPoints.subalgebra R A G)
    (hcover : ∀ p : PrimeSpectrum (FixedPoints.subalgebra R A G),
      ∃ i : ι, p ∈ (PrimeSpectrum.basicOpen (H i) :
        Set (PrimeSpectrum (FixedPoints.subalgebra R A G)))) :
    Ideal.span (Set.range H) = ⊤ := by
  classical
  have hsup : (⨆ i : ι,
      PrimeSpectrum.basicOpen (H i) : TopologicalSpace.Opens
        (PrimeSpectrum (FixedPoints.subalgebra R A G))) = ⊤ := by
    ext p
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨i, hi⟩ := hcover p
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  exact (PrimeSpectrum.iSup_basicOpen_eq_top_iff (f := H)).mp hsup

/-- The actual affine quotient chart-cover data constructed from the refined
quotient cover. -/
theorem affineQuotientChartCoverData_exists :
    Nonempty (AffineQuotientChartCoverData (R := R) (A := A) (G := G)) := by
  classical
  obtain ⟨K, Hq, _hopen, hcover⟩ :=
    quotient_chart_cover_from_refinement (R := R) (A := A) (G := G)
  letI : Fintype K := inferInstance
  have hspan : Ideal.span (Set.range Hq) = ⊤ :=
    ideal_span_range_eq_top_of_cover (R := R) (A := A) (G := G) Hq hcover
  exact ⟨AffineQuotientChartCoverData.ofFamily (R := R) (A := A) (G := G) Hq hspan⟩

/-- The chart cover data has finite index, unit-ideal generation, a covering
family, and affine chart pieces. -/
theorem affineQuotientChartCoverData_spec
    (D : AffineQuotientChartCoverData (R := R) (A := A) (G := G)) :
    Finite D.cover.index ∧
      Ideal.span (Set.range D.cover.element) = ⊤ ∧
      (⨆ i : D.cover.index,
        quotientPiecePrimeOpen (R := R) (A := A) (G := G)
          (D.cover.element i)) = ⊤ ∧
      (∀ i : D.cover.index,
        IsAffineOpen (quotientPieceOpen (R := R) (A := A) (G := G)
          (D.cover.element i))) :=
  ⟨D.finite_index, D.cover.spans_top, D.cover.cover_eq_top, D.piece_affine⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientChartCoverDataFromRefinement
