import tmp.sheaf.xif.paper.S2334VerlagerungEqActual
import tmp.sheaf.xif.paper.S2292TransferCompatActual
import tmp.sheaf.xif.paper.S2292TransferCompatActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2336TransferCompActual

universe u

theorem S2336_transfer_comp {G : Type u} [Group G] (H : Subgroup G)
    [H.FiniteIndex] {A B : Type u} [CommGroup A] [CommGroup B]
    (ψ : A →* B) (ϕ : H →* A) (g : G) :
    ψ (MonoidHom.transfer ϕ g) =
      MonoidHom.transfer (ψ.comp ϕ) g := by
  rw [MonoidHom.transfer_def (ϕ := ϕ) (T := default)]
  rw [MonoidHom.transfer_def (ϕ := ψ.comp ϕ) (T := default)]
  exact LeanFormal.IUT.XiFPaper.S2292TransferCompatActual.S2292_map_diff H ψ ϕ default (g • default)

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2292TransferCompatActual
open LeanFormal.IUT.XiFPaper.S2292TransferCompatActual

variable (p : Nat) [Fact (Nat.Prime p)]

theorem S2336_verlagerungOpen_eq (H K : Index p) (h : H ≤ K)
    [Subgroup.FiniteIndex H.toSubgroup] :
    verlagerungOpen p h =
      (Abelianization.map (Subgroup.subgroupOfEquivOfLe h).toMonoidHom).comp
        (Verlagerung.transferAb (H.toSubgroup.subgroupOf K.toSubgroup)) := by
  apply Abelianization.hom_ext
  ext x
  rw [verlagerungOpen]
  simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of]
  rw [Verlagerung.transferAb_of]
  rw [S2336_transfer_comp]
  congr 1

#check S2336_transfer_comp
#check S2336_verlagerungOpen_eq
#print axioms S2336_verlagerungOpen_eq

end LeanFormal.IUT.XiFPaper.S2336TransferCompActual

end