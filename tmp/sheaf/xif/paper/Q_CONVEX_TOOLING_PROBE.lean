import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.Tropical.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers

open MeasureTheory

#check Convex
#check convexHull
#check mem_convexHull_iff
#check Convex.add
#check Convex.smul
#check ConvexBody
#check ConvexBody.convex
#check ConvexBody.isCompact
#check gauge
#check gaugeSeminorm
#check Convex.addHaar_frontier
#check Convex.nullMeasurableSet
#check MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
#check ZLattice.covolume
#check ZLattice.covolume_eq_measure_fundamentalDomain
#check ZLattice.covolume_eq_det
#check ZLattice.covolume_div_covolume_eq_relIndex
#check ZLattice.volume_image_eq_volume_div_covolume
#check ZLattice.covolume.tendsto_card_div_pow
#check MeasureTheory.Measure.addHaar_smul
#check MeasureTheory.Measure.addHaar_smul_of_nonneg
#check MeasureTheory.Measure.addHaar_image_linearMap
#check MeasureTheory.Measure.addHaar_submodule
#check MeasureTheory.Measure.addHaar
#check Tropical
#check Tropical.trop
#check Tropical.untrop
#check_failure Polytope
#check_failure Ehrhart
#check_failure NewtonPolygon
#check_failure NewtonPolytope

variable {p : ℕ} [Fact p.Prime]
#check_failure (inferInstance : PartialOrder ℚ_[p])
#check_failure (inferInstance : SMul ℝ ℚ_[p])
#check_failure (inferInstance : Module ℝ ℚ_[p])
#check_failure (inferInstance : Algebra ℝ ℚ_[p])
#check_failure (Convex ℚ_[p] (Set.univ : Set ℚ_[p]))
