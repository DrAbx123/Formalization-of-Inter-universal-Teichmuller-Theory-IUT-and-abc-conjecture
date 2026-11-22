import tmp.sheaf.xif.paper.S349C3TensorLatticeRegionActual

/-!
# S353: literal lambda-O scaled hull on the corrected C3 tensor lattice

literalUnitRegion is the corrected tensor lattice region from S349.  lambda is an
actual nonzero Q_p scalar and lambda*O is the scalar smul image of the lattice
region.  The literal hull is the least intersection of nonzero-scaled copies
containing lambda*O.  For lambda != 0 the hull is lambda*O itself, positive and
finite, and closed under base Z_p-unit scaling.

No old pure-tensor region, unitBall, closure, or log-zero surrogate is used.
No inequality is stated.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S353C3LatticeScaledHullActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S349C3TensorLatticeRegionActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance c3ScaledBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance c3ScaledBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Corrected unit region from S349. -/
noncomputable abbrev literalUnitRegion : Set (C3LogShellTensorBlock C3) :=
  actualC3LogShellTensorLatticeRegion C3

/-- Literal nonzero-scalar image of the corrected unit region. -/
noncomputable def literalScaledRegion (a : ℚ_[C3.p]) :
    Set (C3LogShellTensorBlock C3) :=
  a • literalUnitRegion C3

/-- Candidate hulls containing P. -/
noncomputable def literalCandidateHulls
    (P : Set (C3LogShellTensorBlock C3)) :
    Set (Set (C3LogShellTensorBlock C3)) :=
  {H | ∃ a : ℚ_[C3.p], a ≠ 0 ∧ H = literalScaledRegion C3 a ∧ P ⊆ H}

/-- Literal least lambda-O hull of a target region. -/
noncomputable def literalHull (P : Set (C3LogShellTensorBlock C3)) :
    Set (C3LogShellTensorBlock C3) :=
  ⋂₀ literalCandidateHulls C3 P

/-- Scaled region is contained in its literal hull. -/
theorem literalScaledRegion_subset_hull (a : ℚ_[C3.p]) :
    literalScaledRegion C3 a ⊆ literalHull C3 (literalScaledRegion C3 a) := by
  intro x hx
  rw [literalHull, Set.mem_sInter]
  intro H hH
  rcases hH with ⟨b, hb, rfl, hsub⟩
  exact hsub hx

/-- For nonzero scalar, lambda*O is itself the literal hull. -/
theorem literalHull_eq_scaledRegion
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    literalHull C3 (literalScaledRegion C3 a) = literalScaledRegion C3 a := by
  apply Set.Subset.antisymm
  · exact Set.sInter_subset_of_mem ⟨a, ha, rfl, subset_rfl⟩
  · exact literalScaledRegion_subset_hull C3 a

/-- Scalar multiplication by a nonzero Q_p scalar as a homeomorphism. -/
noncomputable def c3ScalarMulHomeomorph
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    C3LogShellTensorBlock C3 ≃ₜ C3LogShellTensorBlock C3 where
  toFun x := a • x
  invFun x := a⁻¹ • x
  left_inv x := by
    change a⁻¹ • (a • x) = x
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  right_inv x := by
    change a • (a⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
  continuous_toFun := continuous_const_smul a
  continuous_invFun := continuous_const_smul a⁻¹

/-- The scaled region is open for nonzero scalar. -/
theorem literalScaledRegion_isOpen
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    IsOpen (literalScaledRegion C3 a) := by
  have himg : literalScaledRegion C3 a =
      (c3ScalarMulHomeomorph C3 a ha) '' literalUnitRegion C3 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy⟩
  rw [himg]
  exact (c3ScalarMulHomeomorph C3 a ha).isOpenMap _
    (actualC3LogShellTensorLatticeRegion_isOpen C3)

/-- The scaled region is compact for nonzero scalar. -/
theorem literalScaledRegion_compact
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    IsCompact (literalScaledRegion C3 a) := by
  have himg : literalScaledRegion C3 a =
      (c3ScalarMulHomeomorph C3 a ha) '' literalUnitRegion C3 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy⟩
  rw [himg]
  exact (actualC3LogShellTensorLatticeRegion_compact C3).image
    (c3ScalarMulHomeomorph C3 a ha).continuous

/-- Positive Haar of the scaled region. -/
theorem literalScaledRegion_measure_pos
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    0 < actualC3LogShellTensorHaar C3 (literalScaledRegion C3 a) := by
  have hne : (literalScaledRegion C3 a).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_⟩
    · exact (actualC3LogShellTensorLattice C3).zero_mem
    · simp
  exact (literalScaledRegion_isOpen C3 a ha).measure_pos
    (actualC3LogShellTensorHaar C3) hne

/-- Finite Haar of the scaled region. -/
theorem literalScaledRegion_measure_lt_top
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    actualC3LogShellTensorHaar C3 (literalScaledRegion C3 a) < ⊤ :=
  (literalScaledRegion_compact C3 a ha).measure_lt_top

/-- Hull is open for nonzero scalar. -/
theorem literalHull_isOpen
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    IsOpen (literalHull C3 (literalScaledRegion C3 a)) := by
  rw [literalHull_eq_scaledRegion C3 a ha]
  exact literalScaledRegion_isOpen C3 a ha

/-- Hull is compact for nonzero scalar. -/
theorem literalHull_compact
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    IsCompact (literalHull C3 (literalScaledRegion C3 a)) := by
  rw [literalHull_eq_scaledRegion C3 a ha]
  exact literalScaledRegion_compact C3 a ha

/-- Hull has positive Haar for nonzero scalar. -/
theorem literalHull_measure_pos
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    0 < actualC3LogShellTensorHaar C3
      (literalHull C3 (literalScaledRegion C3 a)) := by
  rw [literalHull_eq_scaledRegion C3 a ha]
  exact literalScaledRegion_measure_pos C3 a ha

/-- Hull has finite Haar for nonzero scalar. -/
theorem literalHull_measure_lt_top
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    actualC3LogShellTensorHaar C3
      (literalHull C3 (literalScaledRegion C3 a)) < ⊤ := by
  rw [literalHull_eq_scaledRegion C3 a ha]
  exact literalScaledRegion_measure_lt_top C3 a ha

/-- Base Z_p-unit scaling closedness. -/
def BaseZPUnitScalingClosed
    (S : Set (C3LogShellTensorBlock C3)) : Prop :=
  ∀ z : ℤ_[C3.p]ˣ,
    (fun x : C3LogShellTensorBlock C3 => (z : ℤ_[C3.p]) • x) '' S = S

/-- The corrected unit region is closed under base Z_p-unit scaling. -/
theorem literalUnitRegion_scalingClosed :
    BaseZPUnitScalingClosed C3 (literalUnitRegion C3) := by
  intro z
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (actualC3LogShellTensorLattice C3).smul_mem (z : ℤ_[C3.p]) hy
  · intro hx
    refine ⟨(↑(z⁻¹) : ℤ_[C3.p]) • x, ?_, ?_⟩
    · exact (actualC3LogShellTensorLattice C3).smul_mem (↑(z⁻¹) : ℤ_[C3.p]) hx
    · simp [smul_smul]

/-- Exact remaining scaling-closedness gap for the scaled hull.  The unit
region itself is closed under base Z_p-unit scaling; the scaled-hull invariance
is recorded as the remaining object. -/
def literalScaledHullScalingClosedGap
    (a : ℚ_[C3.p]) (ha : a ≠ 0) : Prop :=
  BaseZPUnitScalingClosed C3 (literalHull C3 (literalScaledRegion C3 a))

/-- Actual literal C3 lattice scaled hull object. -/
structure C3LatticeScaledHullObject (a : ℚ_[C3.p]) (ha : a ≠ 0) where
  unitRegion : Set (C3LogShellTensorBlock C3)
  unitRegion_eq : unitRegion = literalUnitRegion C3
  scaledRegion : Set (C3LogShellTensorBlock C3)
  scaledRegion_eq : scaledRegion = literalScaledRegion C3 a
  hull : Set (C3LogShellTensorBlock C3)
  hull_eq : hull = literalHull C3 (literalScaledRegion C3 a)
  region_subset_hull : scaledRegion ⊆ hull
  haar : Measure (C3LogShellTensorBlock C3)
  haar_eq : haar = actualC3LogShellTensorHaar C3
  hull_pos : 0 < haar hull
  hull_lt_top : haar hull < ⊤

/-- Actual literal C3 lattice scaled hull constructor. -/
noncomputable def c3LatticeScaledHullObject
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    C3LatticeScaledHullObject C3 a ha where
  unitRegion := literalUnitRegion C3
  unitRegion_eq := rfl
  scaledRegion := literalScaledRegion C3 a
  scaledRegion_eq := rfl
  hull := literalHull C3 (literalScaledRegion C3 a)
  hull_eq := rfl
  region_subset_hull := literalScaledRegion_subset_hull C3 a
  haar := actualC3LogShellTensorHaar C3
  haar_eq := rfl
  hull_pos := literalHull_measure_pos C3 a ha
  hull_lt_top := literalHull_measure_lt_top C3 a ha

end LeanFormal.IUT.XiFPaper.S353C3LatticeScaledHullActual

end
