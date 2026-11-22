import Mathlib
import LeanFormal.IUT.Foundations.MeasureTheory.CompactOpenAddSubgroupIndex

/-!
# A-Index: lattice orbit index tool (task-77, P3 route-1 tool)

Partial tool file: A1 (second iso, Submodule form), A2 (actual Haar index
formula for L <= K), A3 one-step log-volume increment, and the set-level
scalar-commutation core of A8.  The remaining measure-ratio form of A8
and the A4 product identity are recorded as targets in
coord/ROUTE1-INDEX-TOOL.md (PENDING; no sorry/axiom in this file).
-/

noncomputable section
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1LatticeOrbitIndexActual

/-! ### (A1) second isomorphism, Submodule normal form -/

section SecondIso
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- (A1) `B/(B∩A) ≅ (B+A)/A`.  `comap B.subtype B = ⊤`, so the domain is
`B/(B∩A)` in the subtype normal form used by Mathlib. -/
noncomputable def latticeStepQuotientEquiv (A B : Submodule R M) :
    (B ⧸ (Submodule.comap B.subtype B ⊓ Submodule.comap B.subtype A)) ≃ₗ[R]
      ((B ⊔ A : Submodule R M) ⧸ Submodule.comap (B ⊔ A : Submodule R M).subtype A) :=
  LinearMap.quotientInfEquivSupQuotient B A

end SecondIso

/-! ### (A2) Haar index formula -/

section HaarIndex
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [MeasurableSpace E] [BorelSpace E]

/-- `(K : L)` lattice index, equal to `intersectionIndex K L`. -/
def latticeIndex (L K : AddSubgroup E) : ℕ :=
  LeanFormal.IUT.CompactOpenAddSubgroup.intersectionIndex K L

/-- (A2) for compact open `L ≤ K`: `μ K = #(K/L) * μ L`. -/
theorem haar_measure_eq_index_mul_of_le
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {L K : AddSubgroup E} (hLK : L ≤ K)
    (hLc : IsCompact (L : Set E)) (hLo : IsOpen (L : Set E))
    (hKc : IsCompact (K : Set E)) (hKo : IsOpen (K : Set E)) :
    μ (K : Set E) = (latticeIndex L K : ENNReal) * μ (L : Set E) := by
  have h := LeanFormal.IUT.CompactOpenAddSubgroup.measure_eq_index_mul_intersection
    K L hKc hKo hLo μ
  have hInt : (K : Set E) ∩ (L : Set E) = (L : Set E) := by
    ext x; constructor
    · rintro ⟨-, hx⟩; exact hx
    · intro hx; exact ⟨hLK hx, hx⟩
  rw [hInt] at h
  simpa [latticeIndex] using h

/-- Normalized log-volume `(1/d)·log μ(L)`. -/
def normalizedLogVolume (μ : Measure E) (d : ℕ) (L : AddSubgroup E) : ℝ :=
  (1 / (d : ℝ)) * Real.log (μ (L : Set E)).toReal

/-- (A3) one-step log-volume increment: `λ(K)-λ(L) = (1/d)·log #(K/L)`. -/
theorem normalizedLogVolume_step
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (d : ℕ) {L K : AddSubgroup E} (hLK : L ≤ K)
    (hLc : IsCompact (L : Set E)) (hLo : IsOpen (L : Set E))
    (hKc : IsCompact (K : Set E)) (hKo : IsOpen (K : Set E))
    (hLpos : 0 < μ (L : Set E)) (hLtop : μ (L : Set E) < ⊤) :
    normalizedLogVolume μ d K - normalizedLogVolume μ d L =
      (1 / (d : ℝ)) * Real.log (latticeIndex L K : ℝ) := by
  have hmeas := haar_measure_eq_index_mul_of_le μ hLK hLc hLo hKc hKo
  have hi : (latticeIndex L K : ℝ) ≠ 0 := by
    exact_mod_cast (LeanFormal.IUT.CompactOpenAddSubgroup.intersectionIndex_pos K L hKc hLo).ne'
  have hL0 : (μ (L : Set E)).toReal ≠ 0 := (ENNReal.toReal_pos hLpos.ne' hLtop.ne).ne'
  have harg : (μ (K : Set E)).toReal =
      (latticeIndex L K : ℝ) * (μ (L : Set E)).toReal := by
    rw [hmeas, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_natCast]
  have hlog : Real.log (μ (K : Set E)).toReal =
      Real.log (latticeIndex L K : ℝ) + Real.log (μ (L : Set E)).toReal := by
    rw [harg, Real.log_mul hi hL0]
  unfold normalizedLogVolume
  rw [hlog]
  ring

end HaarIndex

/-! ### (A8) scalar commutation (set level) -/

section ScalarOrbit
variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]

/-- Scalar multiplication by a nonzero field element, as an additive equivalence. -/
def scalarAddEquiv (c : F) (hc : c ≠ 0) : E ≃+ E where
  toFun x := c • x
  invFun x := c⁻¹ • x
  left_inv x := by simp [hc]
  right_inv x := by simp [hc]
  map_add' x y := by simp [smul_add]

/-- Scalar image of a lattice. -/
def scalarLattice (c : F) (hc : c ≠ 0) (L : AddSubgroup E) : AddSubgroup E :=
  L.map (scalarAddEquiv c hc).toAddMonoidHom

/-- (A8, set core) If `g` commutes with the scalar `c`, then the `g`-image of
the scalar lattice is the scalar image of the `g`-image. -/
theorem orbit_scalar_comm (c : F) (hc : c ≠ 0) (g : E ≃+ E)
    (hg : ∀ x, g (c • x) = c • g x) (L : AddSubgroup E) :
    scalarLattice c hc (L.map g.toAddMonoidHom) =
      (scalarLattice c hc L).map g.toAddMonoidHom := by
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨c • z, ⟨z, hz, rfl⟩, hg z⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨g z, ?_, ?_⟩
    · exact ⟨z, hz, rfl⟩
    · change c • g z = g (c • z)
      exact (hg z).symm

end ScalarOrbit

end LeanFormal.IUT.XiFPaper.Mzk1LatticeOrbitIndexActual
