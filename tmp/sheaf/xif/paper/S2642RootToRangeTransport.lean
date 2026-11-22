import tmp.sheaf.xif.paper.S2446RangeCycleTypeSubagentActual

/-! # S2642: {2,10} root-to-range transport (pair/root bridge) -/

noncomputable section
set_option maxHeartbeats 4000000

open LeanFormal.IUT.XiFPaper.S2446RangeCycleTypeSubagentActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual

namespace LeanFormal.IUT.XiFPaper.S2642RootToRangeTransport

theorem S2642PairMap_injective (σ : S1725AbsoluteGalois) :
    Function.Injective (S2056PairMap σ) := by
  intro S T hST
  have hf : Function.Injective (S2056NonzeroTorsionMap σ) :=
    S2056NonzeroTorsionMap_injective σ
  have himg : S.1.image (S2056NonzeroTorsionMap σ) =
      T.1.image (S2056NonzeroTorsionMap σ) :=
    congrArg Subtype.val hST
  apply Subtype.ext
  exact (Finset.image_inj hf).mp himg

noncomputable def S2642PairPerm (σ : S1725AbsoluteGalois) : Equiv.Perm S2056Pair :=
  Equiv.ofBijective (S2056PairMap σ)
    (Finite.injective_iff_bijective.mp (S2642PairMap_injective σ))

noncomputable def S2642RootPerm (σ : S1725AbsoluteGalois) : Equiv.Perm S2056Root :=
  Equiv.ofBijective (S2056RootMap σ)
    (Finite.injective_iff_bijective.mp (by
      intro x y h
      apply Subtype.ext
      exact σ.injective (congrArg Subtype.val h)))

noncomputable def S2642PairEquiv : S2009Pairs ≃ S2056Pair :=
  Equiv.ofBijective (S2180PairMap S2172AffineBasis)
    (S2186PairMap_bijective S2172AffineBasis)

theorem S2642cycleType_permCongr {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  classical
  have hperm : e.permCongr σ =
      σ.extendDomain (e.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm) := by
    ext b
    rw [Equiv.Perm.extendDomain_apply_subtype (h := trivial), Equiv.permCongr_apply]
    rfl
  rw [hperm]
  exact Equiv.Perm.cycleType_extendDomain _

theorem S2642PairMatrix_cycleType (σ : S1725AbsoluteGalois) :
    (pairPermHom
      (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).cycleType =
      (S2642PairPerm σ).cycleType := by
  have hconj : S2642PairEquiv.permCongr
      (pairPermHom (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)) =
        S2642PairPerm σ := by
    apply Equiv.ext
    intro x
    have happ : S2642PairEquiv (S2642PairEquiv.symm x) = x :=
      Equiv.apply_symm_apply _ x
    change S2180PairMap S2172AffineBasis
      (pairAct (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)
        (S2642PairEquiv.symm x)) = S2056PairMap σ x
    rw [S2446PairAction_apply]
    change S2056PairMap σ (S2642PairEquiv (S2642PairEquiv.symm x)) = S2056PairMap σ x
    rw [happ]
  rw [← hconj, S2642cycleType_permCongr]

theorem S2642PairPerm_cycleType_eq_rootPerm (σ : S1725AbsoluteGalois) :
    (S2642PairPerm σ).cycleType = (S2642RootPerm σ).cycleType := by
  have hconj : S2056RootPairEquiv.permCongr (S2642RootPerm σ) = S2642PairPerm σ := by
    apply Equiv.ext
    intro x
    have happ : S2056RootPairEquiv (S2056RootPairEquiv.symm x) = x :=
      Equiv.apply_symm_apply _ x
    change S2056RootPairEquiv (S2056RootMap σ (S2056RootPairEquiv.symm x)) =
      S2056PairMap σ x
    rw [S2056RootPairEquiv_equivariant]
    change S2056PairMap σ (S2056RootPairEquiv (S2056RootPairEquiv.symm x)) =
      S2056PairMap σ x
    rw [happ]
  rw [← hconj, S2642cycleType_permCongr]

theorem S2642RootMapToRangeTransport (σ : S1725AbsoluteGalois)
    (h : (S2642RootPerm σ).cycleType = ({10, 2} : Multiset ℕ)) :
    S2203RangeCycleTypeRequired S1982Basis := by
  change S2446Target
  rw [S2446Target_iff_exists_galois]
  refine ⟨σ, ?_⟩
  rw [S2642PairMatrix_cycleType, S2642PairPerm_cycleType_eq_rootPerm]
  exact h

#check S2642RootMapToRangeTransport
#print axioms S2642RootMapToRangeTransport

end LeanFormal.IUT.XiFPaper.S2642RootToRangeTransport
end
