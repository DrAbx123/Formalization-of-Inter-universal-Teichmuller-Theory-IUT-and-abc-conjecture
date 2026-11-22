import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductLogVolumeTransport

/-!
# Packet normalization of actual finite p-adic product-field volumes

Divide the unit-relative Haar log-mass by the actual Qp dimension. For a
nonempty finite product of finite extension fields this dimension is
positive, and multiplication by p adds exactly -log p, as in III 3.9(i).
The zero-dimensional case is excluded from that scaling assertion.

This is uniform dimension normalization. The selected-place weights in
III Remark 3.1.1(ii), involving local degrees over Fmod, require an
additional construction; the p-scaling property alone does not identify
this functional with that weighted logarithmic volume.
-/

namespace LeanFormal.IUT.LocalFieldProductHull

open MeasureTheory
open scoped Pointwise

noncomputable section

variable {p : ℕ} [Fact p.Prime] {J : Type*} (E : J → Type*)
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [MeasurableSpace ((j : J) → E j)]

def padicPacketLogVolume (μ : Measure ((j : J) → E j)) (S : Set ((j : J) → E j)) : ℝ :=
  normalizedLogVolume μ S / (Module.finrank ℚ_[p] ((j : J) → E j) : ℝ)

theorem padicPacketLogVolume_unitRegion (μ : Measure ((j : J) → E j)) :
    padicPacketLogVolume (p := p) E μ (unitRegion (K := E)) = 0 := by
  simp only [padicPacketLogVolume, normalizedLogVolume_unitRegion, zero_div]

variable [Finite J] [∀ j, FiniteDimensional ℚ_[p] (E j)]
variable [BorelSpace ((j : J) → E j)]

theorem padicPacketLogVolume_prime_smul [Nonempty J]
    (μ : Measure ((j : J) → E j)) [Measure.IsAddHaarMeasure μ]
    {S : Set ((j : J) → E j)} (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    padicPacketLogVolume (p := p) E μ ((p : ℚ_[p]) • S) =
      -Real.log (p : ℝ) + padicPacketLogVolume (p := p) E μ S := by
  classical
  letI := Fintype.ofFinite J
  let coordinate : J := Classical.choice ‹Nonempty J›
  letI : Nontrivial ((j : J) → E j) :=
    ⟨⟨0, 1, fun heq => zero_ne_one (congrArg (fun x => x coordinate) heq)⟩⟩
  have hdim : (Module.finrank ℚ_[p] ((j : J) → E j) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)
  have hlog := FinitePadicHaarScaling.log_measure_prime_smul_finiteDimensional
    (p := p) μ hpos hfin
  unfold padicPacketLogVolume normalizedLogVolume
  rw [hlog]
  field_simp
  ring

theorem padicPacketLogVolume_mul_prime [Nonempty J]
    (μ : Measure ((j : J) → E j)) [Measure.IsAddHaarMeasure μ]
    {S : Set ((j : J) → E j)} (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    padicPacketLogVolume (p := p) E μ
      ((fun x : (j : J) → E j => (p : (j : J) → E j) * x) '' S) =
      -Real.log (p : ℝ) + padicPacketLogVolume (p := p) E μ S := by
  have hmul : (fun x : (j : J) → E j => (p : (j : J) → E j) * x) =
      (fun x => (p : ℚ_[p]) • x) := by
    funext x
    rw [Algebra.smul_def, map_natCast]
  rw [hmul]
  exact padicPacketLogVolume_prime_smul E μ hpos hfin

variable {L : Type*} [Finite L] {F : L → Type*}
variable [∀ l, NormedField (F l)] [∀ l, NormedAlgebra ℚ_[p] (F l)]
variable [∀ l, FiniteDimensional ℚ_[p] (F l)]
variable [∀ j, ProperSpace (E j)] [∀ l, ProperSpace (F l)]
variable [MeasurableSpace ((l : L) → F l)] [BorelSpace ((l : L) → F l)]

omit [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ l, FiniteDimensional ℚ_[p] (F l)] in
theorem padicPacketLogVolume_algEquiv
    (e : ((j : J) → E j) ≃ₐ[ℚ_[p]] ((l : L) → F l))
    (he : Continuous e) (hinverse : Continuous e.symm)
    (μ : Measure ((j : J) → E j)) (ν : Measure ((l : L) → F l))
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {S : Set ((j : J) → E j)} (hS : IsCompact (closure S)) (hpos : 0 < μ S) :
    padicPacketLogVolume (p := p) F ν (e '' S) = padicPacketLogVolume (p := p) E μ S := by
  have hlog := normalizedLogVolume_continuous_ringEquiv e.toRingEquiv he hinverse μ ν hS hpos
  change normalizedLogVolume ν (e '' S) = normalizedLogVolume μ S at hlog
  unfold padicPacketLogVolume
  rw [hlog, e.toLinearEquiv.finrank_eq]

end

end LeanFormal.IUT.LocalFieldProductHull
