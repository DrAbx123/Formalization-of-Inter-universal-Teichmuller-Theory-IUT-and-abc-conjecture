import tmp.sheaf.xif.paper.Mzk1DiagEmbeddingEquivActual

/-! CONDITIONAL/construction: `(d → Z_p) ≃ₗ coordSmall`, and the embedding
maps `∏ p^{f_i} Z_p` (integer ambient) to `∏ p^{f_i} Z_p` (Q_p ambient).
No sorry/axiom. The quotient map/mapQ step is GAP. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1DiagEquivProvedActual

open LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual

variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]

def embLinear : (d → PadicInt p) →ₗ[PadicInt p] (d → ℚ_[p]) where
  toFun := integerProductEmbedding (p := p) (d := d)
  map_add' x y := by funext i; simp [integerProductEmbedding, map_add]
  map_smul' c x := by funext i; simp [integerProductEmbedding, Algebra.smul_def, mul_comm]

theorem embLinear_apply_mem (x : d → PadicInt p) :
    embLinear (p := p) (d := d) x ∈ coordSmall (p := p) (d := d) := by
  rw [coordSmall, Submodule.mem_pi]
  intro i _
  rw [Submodule.mem_span_singleton]
  exact ⟨x i, by simp [embLinear, integerProductEmbedding, Algebra.smul_def]⟩

theorem embLinear_injective :
    Function.Injective (embLinear (p := p) (d := d)) := by
  intro x y h; funext i
  exact Subtype.ext (by simpa [embLinear, integerProductEmbedding] using congrFun h i)

theorem embLinear_range :
    Set.range (embLinear (p := p) (d := d)) =
      (coordSmall (p := p) (d := d) : Set (d → ℚ_[p])) := by
  ext y; constructor
  · rintro ⟨x, rfl⟩; exact embLinear_apply_mem x
  · intro hy
    have hy' : ∀ i, y i ∈ Submodule.span (PadicInt p) {(1 : ℚ_[p])} := by
      simpa [coordSmall, Submodule.mem_pi] using hy
    choose z hz using fun i => Submodule.mem_span_singleton.mp (hy' i)
    refine ⟨fun i => z i, ?_⟩
    funext i
    have hz' : algebraMap (PadicInt p) ℚ_[p] (z i) = y i := by
      simpa [Algebra.smul_def] using hz i
    simpa [embLinear, integerProductEmbedding] using hz'

def toCoordSmall : (d → PadicInt p) →ₗ[PadicInt p] coordSmall (p := p) (d := d) :=
  (embLinear (p := p) (d := d)).codRestrict (coordSmall (p := p) (d := d))
    (fun x => embLinear_apply_mem (p := p) (d := d) x)

theorem toCoordSmall_bijective :
    Function.Bijective (toCoordSmall (p := p) (d := d)) := by
  constructor
  · intro x y h
    apply embLinear_injective (p := p) (d := d)
    exact congrArg (fun z : coordSmall (p := p) (d := d) => (z : d → ℚ_[p])) h
  · intro y
    have hy : (y : d → ℚ_[p]) ∈ Set.range (embLinear (p := p) (d := d)) := by
      rw [embLinear_range]; exact y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    apply Subtype.ext
    simpa [toCoordSmall, embLinear] using hx

noncomputable def integerProductEquiv :
    (d → PadicInt p) ≃ₗ[PadicInt p] coordSmall (p := p) (d := d) :=
  LinearEquiv.ofBijective (toCoordSmall (p := p) (d := d))
    (toCoordSmall_bijective (p := p) (d := d))

/-- The embedding maps the integer-ambient dual lattice onto the Q_p-ambient one. -/
theorem embLinear_map_coordDualInt (f : d → Nat) :
    Submodule.map (embLinear (p := p) (d := d))
        (coordDualInt (p := p) (d := d) f) = coordDual (p := p) (d := d) f := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [coordDual, Submodule.mem_pi]
    intro i _
    have hxpi : x ∈ Submodule.pi Set.univ
        (fun i => Ideal.span ({(p : PadicInt p) ^ (f i)} : Set (PadicInt p))) := by
      simpa [coordDualInt, LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual.diagLatticeSubmodule] using hx
    have hxi : x i ∈ Ideal.span ({(p : PadicInt p) ^ (f i)} : Set (PadicInt p)) :=
      (Submodule.mem_pi.mp hxpi) i (Set.mem_univ i)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hxi
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    simp [embLinear, integerProductEmbedding, hc, Algebra.smul_def, map_mul,
      mul_comm, mul_left_comm, mul_assoc]
  · intro hy
    have hy' : ∀ i, y i ∈ Submodule.span (PadicInt p) {((p : ℚ_[p]) ^ (f i))} := by
      simpa [coordDual, Submodule.mem_pi] using hy
    choose r hr using fun i =>
      Submodule.mem_span_singleton.mp (hy' i)
    let x : d → PadicInt p := fun i => r i * (p : PadicInt p) ^ (f i)
    refine ⟨x, ?_, ?_⟩
    · have hxpi : x ∈ Submodule.pi Set.univ
          (fun i => Ideal.span ({(p : PadicInt p) ^ (f i)} : Set (PadicInt p))) := by
        rw [Submodule.mem_pi]
        intro i _
        rw [Ideal.mem_span_singleton]
        exact ⟨r i, by simp [x, mul_comm]⟩
      simpa [coordDualInt, LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual.diagLatticeSubmodule] using hxpi
    · funext i
      have hr' : r i • ((p : ℚ_[p]) ^ (f i)) = y i := hr i
      change algebraMap (PadicInt p) ℚ_[p] (x i) = y i
      rw [show x i = r i * (p : PadicInt p) ^ (f i) from rfl, map_mul]
      simpa [Algebra.smul_def] using hr'



end LeanFormal.IUT.XiFPaper.Mzk1DiagEquivProvedActual
end  