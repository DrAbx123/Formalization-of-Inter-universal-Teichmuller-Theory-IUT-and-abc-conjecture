import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientDataFromInvariants
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affineness of the source chart overlap

For a separated ambient scheme, the intersection of the two affine chart opens is
affine. The source overlap is the pullback of the two chart open immersions; its
first projection composed with the first chart is an open immersion whose range is
that intersection. Hence the source overlap is isomorphic to the intersection
open subscheme, and is affine.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceOverlapIntersectionIso

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientDataFromInvariants

/-- The intersection of the two affine chart opens. -/
noncomputable def overlapOpen (C : SourceChartFamily) (i j : C.J) : C.X.Opens :=
  letI : IsOpenImmersion (C.chartι i) := C.chart_open i
  letI : IsOpenImmersion (C.chartι j) := C.chart_open j
  (C.chartι i).opensRange ⊓ (C.chartι j).opensRange

/-- The pullback first projection composed with the first chart. -/
noncomputable def overlapOpenImmersion (C : SourceChartFamily) (i j : C.J) :
    pullback (C.chartι i) (C.chartι j) ⟶ C.X :=
  letI := C.hasPullback i j
  letI : IsOpenImmersion (C.chartι i) := C.chart_open i
  letI : IsOpenImmersion (C.chartι j) := C.chart_open j
  pullback.fst (C.chartι i) (C.chartι j) ≫ C.chartι i

theorem overlapOpenImmersion_isOpenImmersion
    (C : SourceChartFamily) (i j : C.J) :
    IsOpenImmersion (overlapOpenImmersion C i j) := by
  letI := C.hasPullback i j
  haveI : IsOpenImmersion (C.chartι i) := C.chart_open i
  haveI : IsOpenImmersion (C.chartι j) := C.chart_open j
  haveI : IsOpenImmersion (pullback.fst (C.chartι i) (C.chartι j)) := inferInstance
  exact IsOpenImmersion.comp (pullback.fst (C.chartι i) (C.chartι j)) (C.chartι i)

theorem overlapOpenImmersion_range
    (C : SourceChartFamily) (i j : C.J) :
    Set.range (overlapOpenImmersion C i j) = (overlapOpen C i j : Set C.X) := by
  letI := C.hasPullback i j
  haveI : IsOpenImmersion (C.chartι i) := C.chart_open i
  haveI : IsOpenImmersion (C.chartι j) := C.chart_open j
  rw [overlapOpenImmersion, IsOpenImmersion.range_pullback_to_base_of_left]
  ext x
  simp [overlapOpen, Scheme.Hom.coe_opensRange]

/-- The actual isomorphism from the source overlap to the intersection open
subscheme. -/
noncomputable def sourceOverlapIntersectionIso
    (C : SourceChartFamily) (i j : C.J) :
    pullback (C.chartι i) (C.chartι j) ≅ (overlapOpen C i j).toScheme :=
  letI := C.hasPullback i j
  haveI : IsOpenImmersion (overlapOpenImmersion C i j) :=
    overlapOpenImmersion_isOpenImmersion C i j
  IsOpenImmersion.isoOfRangeEq (overlapOpenImmersion C i j)
    (overlapOpen C i j).ι (by
      simpa [Scheme.Opens.range_ι] using overlapOpenImmersion_range C i j)

theorem diagonal_isAffineHom (C : SourceChartFamily) (hsep : C.X.IsSeparated) :
    IsAffineHom (pullback.diagonal (terminal.from C.X)) := by
  letI : C.X.IsSeparated := hsep
  haveI : IsSeparated (terminal.from C.X) := inferInstance
  haveI : IsClosedImmersion (pullback.diagonal (terminal.from C.X)) := inferInstance
  infer_instance

theorem overlapOpen_isAffine (C : SourceChartFamily) (i j : C.J)
    (hsep : C.X.IsSeparated) :
    IsAffineOpen (overlapOpen C i j) := by
  haveI : IsAffineHom (pullback.diagonal (terminal.from C.X)) :=
    diagonal_isAffineHom C hsep
  haveI : IsAffine (C.U i) := C.chart_affine i
  haveI : IsAffine (C.U j) := C.chart_affine j
  haveI : IsOpenImmersion (C.chartι i) := C.chart_open i
  haveI : IsOpenImmersion (C.chartι j) := C.chart_open j
  exact IsAffineOpen.inf
    (isAffineOpen_opensRange (C.chartι i))
    (isAffineOpen_opensRange (C.chartι j))

theorem pullback_isAffine (C : SourceChartFamily) (i j : C.J)
    (hsep : C.X.IsSeparated) :
    IsAffine (pullback (C.chartι i) (C.chartι j)) := by
  letI := C.hasPullback i j
  letI : IsAffine ((overlapOpen C i j).toScheme) :=
    overlapOpen_isAffine C i j hsep
  exact IsAffine.of_isIso (sourceOverlapIntersectionIso C i j).hom

/-- The source overlap itself is affine. -/
theorem sourceOverlap_isAffine (C : SourceChartFamily) (i j : C.J)
    (hsep : C.X.IsSeparated) :
    IsAffine (sourceOverlap C i j) := by
  letI := C.hasPullback i j
  change IsAffine (pullback (C.chartι i) (C.chartι j))
  exact pullback_isAffine C i j hsep

/-- Affine source overlap instance under separatedness. -/
instance sourceOverlapAffine (C : SourceChartFamily) (i j : C.J)
    [C.X.IsSeparated] : IsAffine (sourceOverlap C i j) :=
  sourceOverlap_isAffine C i j inferInstance

end LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceOverlapIntersectionIso
end
