/- U-R Phi action (small): source action family into p6Phi with lattice
preservation. -/
import tmp.sheaf.xif.paper.URPacketDefs
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import tmp.sheaf.xif.paper.Mzk1P6PhiActionSourceActual
import tmp.sheaf.n8.closure.NativeInput
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.URPhiAction
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionSourceActual
open LeanFormal.IUT.XiFPaper.URPacketDefs

universe u v w
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [MeasurableSpace (urBlock X)] [BorelSpace (urBlock X)]

def urPhi : Set (urBlock X ≃ₗ[ℚ_[urP X]] urBlock X) :=
  p6Phi (urPlaces X) (urTuple X)

theorem urPhi_preserves
    {phi : urBlock X ≃ₗ[ℚ_[urP X]] urBlock X} (hphi : phi ∈ urPhi X) :
    ∀ u, u ∈ urReferenceLattice X → phi u ∈ urReferenceLattice X :=
  p6Phi_preserves (urPlaces X) (urTuple X) hphi

theorem urPhi_nonempty : (urPhi X).Nonempty := by
  refine ⟨LinearEquiv.refl ℚ_[urP X] (urBlock X), ?_⟩
  intro u hu
  simpa using hu

noncomputable def urSourceArrowData :
    PhiActionSourceData (urPlaces X) (urTuple X) :=
  phiActionSourceData (urPlaces X) (urTuple X)

theorem urId_mem_phi :
    (LinearEquiv.refl ℚ_[urP X] (urBlock X)) ∈ urPhi X :=
  (urSourceArrowData X).id_mem

theorem urSourceArrow_preserves :
    ∀ phi ∈ (urSourceArrowData X).Phi,
      ∀ u, u ∈ urReferenceLattice X → phi u ∈ urReferenceLattice X :=
  (urSourceArrowData X).preserves

#print axioms urPhi_preserves
end LeanFormal.IUT.XiFPaper.URPhiAction
end
