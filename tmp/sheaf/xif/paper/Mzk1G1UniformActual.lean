import tmp.sheaf.xif.paper.Mzk1G1BelyiActual
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Finset.Max

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open Polynomial

/-- Actual finite uniform family of Belyi maps over ℚ. -/
structure BelyiUniformFiniteFamily where
  m : ℕ
  degree : ℕ
  map : Fin m → BelyiMapData ℚ
  degree_eq : ∀ i, (map i).poly.natDegree = degree

/-- Single-map compactness bound over ℚ. -/
theorem exists_uniform_derivative_bound_rat
    (p : ℚ[X]) (K : Set ℚ) (hK : IsCompact K)
    (hne : ∀ x ∈ K, p.derivative.eval x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ ‖p.derivative.eval x‖ := by
  have hcont : Continuous (fun x : ℚ => ‖p.derivative.eval x‖) := by fun_prop
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, fun x hx => (False.elim (by simpa using hx))⟩
  · obtain ⟨x0, hx0K, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
    refine ⟨‖p.derivative.eval x0‖, ?_, fun x hx => hmin hx⟩
    exact norm_pos_iff.mpr (hne x0 hx0K)

/-- Actual §13.3 uniform-epsilon theorem for a finite Belyi family over ℚ:
there is one positive δ bounding all derivatives below on a compact set
avoiding every ramification locus. -/
theorem belyi_family_uniform_derivative_bound
    (F : BelyiUniformFiniteFamily) (K : Set ℚ) (hK : IsCompact K)
    (hne : ∀ i x, x ∈ K → (F.map i).poly.derivative.eval x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ i x, x ∈ K → δ ≤ ‖(F.map i).poly.derivative.eval x‖ := by
  by_cases hm : F.m = 0
  · haveI : IsEmpty (Fin F.m) := by
      rw [hm]
      infer_instance
    exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · have hmpos : 0 < F.m := Nat.pos_of_ne_zero hm
    let b : Fin F.m → ℝ := fun i =>
      Classical.choose (exists_uniform_derivative_bound_rat (F.map i).poly K hK
        (fun x hx => hne i x hx))
    have hbpos : ∀ i, 0 < b i := fun i =>
      (Classical.choose_spec (exists_uniform_derivative_bound_rat (F.map i).poly K hK
        (fun x hx => hne i x hx))).1
    obtain ⟨i0, -, hmin⟩ :=
      Finset.univ.exists_min_image b (Finset.univ_nonempty_iff.mpr ⟨⟨0, hmpos⟩⟩)
    refine ⟨b i0, hbpos i0, fun i x hx => ?_⟩
    exact (hmin i (Finset.mem_univ i)).trans
      ((Classical.choose_spec (exists_uniform_derivative_bound_rat (F.map i).poly K hK
        (fun x hx => hne i x hx))).2 x hx)


/-- The actual uniform-epsilon predicate for a Belyi family on a compact set:
one positive δ bounds all derivatives below. -/
def BelyiFamilyUniformEpsilon (F : BelyiUniformFiniteFamily) (K : Set ℚ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ i x, x ∈ K → δ ≤ ‖(F.map i).poly.derivative.eval x‖

/-- Actual proof of the uniform-epsilon predicate from compactness and
nonvanishing of all derivatives. -/
theorem belyiFamily_uniformEpsilon
    (F : BelyiUniformFiniteFamily) (K : Set ℚ) (hK : IsCompact K)
    (hne : ∀ i x, x ∈ K → (F.map i).poly.derivative.eval x ≠ 0) :
    BelyiFamilyUniformEpsilon F K :=
  belyi_family_uniform_derivative_bound F K hK hne

/-- Actual second Belyi map: X^2, ramified only at 0 and ∞. -/
def belyiSquare : BelyiMapData ℚ where
  poly := X ^ 2
  degree_pos := by
    have h : (X ^ 2 : ℚ[X]).natDegree = 2 := by compute_degree!
    rw [h]
    norm_num
  ramified_only_base := by
    intro x hx
    norm_num [Polynomial.derivative_X_pow] at hx
    left
    subst x
    norm_num

/-- An actual non-singleton uniform Belyi family of degree 2. -/
def belyiTwoFamily : BelyiUniformFiniteFamily where
  m := 2
  degree := 2
  map := fun i => if i = 0 then belyiExample else belyiSquare
  degree_eq := by
    intro i
    fin_cases i
    · change (X ^ 2 - 2 * X + C (2 : ℚ)).natDegree = 2
      compute_degree!
    · change (X ^ 2 : ℚ[X]).natDegree = 2
      compute_degree!

/-- Actual nonvacuous uniform-epsilon instance: the two-map Belyi family on
the compact singleton {2}. -/
theorem belyiTwoFamily_uniformEpsilon :
    BelyiFamilyUniformEpsilon belyiTwoFamily ({2} : Set ℚ) := by
  apply belyiFamily_uniformEpsilon
  · exact isCompact_singleton
  · intro i x hx
    fin_cases i
    · simp at hx
      subst x
      simp only [belyiTwoFamily, belyiExample]
      norm_num [Polynomial.derivative_X_pow, Polynomial.derivative_X,
        Polynomial.derivative_C]
    · simp at hx
      subst x
      simp only [belyiTwoFamily, belyiSquare]
      norm_num [Polynomial.derivative_X_pow]

end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
