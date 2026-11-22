import tmp.sheaf.xif.paper.S2736gTensorPKAssemblyActual

noncomputable section
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2736hTensorCharPKFinalActual

open MeasureTheory
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.PadicFiniteCoordinateHaarScaling
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736aCharPKActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2736fTensorPKPiecesActual
open LeanFormal.IUT.XiFPaper.S2736gTensorPKAssemblyActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]

theorem tensor_char_pK (K : ℤ) :
    distribHaarChar (FinitePadicTensor (p := p) M)
      (padicPrimeFieldUnit (p := p) ^ K) =
      ((‖(padicPrimeFieldUnit (p := p) : ℚ_[p])‖₊) ^
        Fintype.card (FinitePadicTensorIndex (p := p) M)) ^ K := by
  obtain ⟨c, hc0, hmap⟩ := tensor_haar_map_exists (p := p) M
  have hpre := tensor_hpre (p := p) M K
  have hLsm := tensor_Lsm (p := p) M K
  have hmapTL := tensor_hmapTL (p := p) M c hmap
  have hmap_pK := tensor_hmap_pK (p := p) M K c hpre hLsm hmap
  have hC := tensor_hC (p := p) M K
  have hratio := tensor_hratio (p := p) M K c
    (distribHaarChar (FinitePadicTensorIndex (p := p) M → ℚ_[p])
      (padicPrimeFieldUnit (p := p) ^ K)) hmapTL hmap_pK hC
  have hmain := tensor_hmain (p := p) M K
    (distribHaarChar (FinitePadicTensorIndex (p := p) M → ℚ_[p])
      (padicPrimeFieldUnit (p := p) ^ K)) hratio
  rw [hmain]
  rw [char_pK (p := p) (ι := FinitePadicTensorIndex (p := p) M) K]
  rw [nnnorm_padicPrimeFieldUnit]
  rw [inv_pow]

#check tensor_char_pK
end LeanFormal.IUT.XiFPaper.S2736hTensorCharPKFinalActual
end
