import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActualTensorSpan
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRegion
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRealization

noncomputable section
open scoped TensorProduct
namespace Probe1445

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldPadicTensor

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [NormedAlgebra ℚ_[p] K] [ProperSpace K]

theorem sourceLogShellStar_eq_logShellScale :
    sourceLogShellStar p = logShellScale p := by
  unfold sourceLogShellStar logShellScale
  rcases (Fact.out : Nat.Prime p).eq_two_or_odd with h2 | hodd
  · subst h2
    norm_num
  · rw [if_pos hodd, if_neg]
    exact fun h => by omega

theorem logShellScale_pos : 0 < logShellScale p := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  unfold logShellScale
  split <;> positivity

abbrev D : SourceLogShellDatum where
  p := p
  hp := Fact.out
  K := K
  fieldK := inferInstance
  charZeroK := inferInstance
  Units := (Integers K)ˣ
  groupUnits := inferInstance
  invariants := ⊤
  logMap := unitLogHom (p := p)

theorem D_logShell_eq :
    (D (p := p) (K := K)).logShell = (integralLogShell (K := K) (p := p) : Set K) := by
  have hD : (D (p := p) (K := K)).logShell =
      {a : K | (sourceLogShellStar p : K) * a ∈ Set.range (fun u : (Integers K)ˣ => unitLog u)} := by
    ext a
    simp [D, SourceLogShellDatum.logShell, SourceLogShellDatum.preLogShell,
      SourceLogShellDatum.pStar, unitLogHom]
  rw [hD]
  ext a
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    change (logShellScale p : K)⁻¹ * unitLog u = a
    have hu' : unitLog u = (sourceLogShellStar p : K) * a := hu
    rw [sourceLogShellStar_eq_logShellScale] at hu'
    rw [hu', ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact Nat.cast_ne_zero.mpr (ne_of_gt logShellScale_pos)
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    change unitLog u = (sourceLogShellStar p : K) * a
    have hu' : (logShellScale p : K)⁻¹ * unitLog u = a := hu
    rw [← hu']
    rw [sourceLogShellStar_eq_logShellScale, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact Nat.cast_ne_zero.mpr (ne_of_gt logShellScale_pos)

theorem D_IQSpan_eq_top :
    (D (p := p) (K := K)).IQSpan = ⊤ := by
  rw [SourceLogShellDatum.IQSpan, D_logShell_eq]
  exact rat_span_integralLogShell_eq_top (p := p) (A := fun _ : Unit => K) ()

end Probe1445
