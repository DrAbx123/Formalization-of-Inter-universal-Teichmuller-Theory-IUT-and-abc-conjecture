import tmp.sheaf.xif.paper.S2501MatrixPairEquivActual
import tmp.sheaf.xif.paper.S2510AbsoluteLiftActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2520RootCycleTransferActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S2501MatrixPairEquivActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2510AbsoluteLiftActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

/-- psi5 over the closure is the base change of the S2057 polynomial. -/
theorem S2520Psi_eq :
    S2056W.preΨ (5 : ℤ) =
      S2057Psi5F.map (algebraMap S1720Field S2056K) := by
  change ((S1667Curve.map (algebraMap ℚ S1720Field)).map
      (algebraMap S1720Field S2056K)).preΨ (5 : ℤ) =
    (((S1667Curve.preΨ (5 : ℤ)).map (algebraMap ℚ S1720Field)).map
      (algebraMap S1720Field S2056K))
  rw [WeierstrassCurve.map_preΨ, WeierstrassCurve.map_preΨ]

/-- The map from the splitting-field roots to the closure roots. -/
noncomputable def S2520RootMap (x : S2132DivisionRoots) : S2056Root :=
  ⟨S2510Embedding x.1, by
    classical
    have hx : Polynomial.aeval x.1 S2057Psi5F = 0 := by
      have hx' := x.2
      rw [Polynomial.mem_rootSet'] at hx'
      exact hx'.2
    rw [S2056RootFinset, Multiset.mem_toFinset, Polynomial.mem_roots S2056W_preΨ_ne_zero]
    change Polynomial.aeval (S2510Embedding x.1) (S2056W.preΨ (5 : ℤ)) = 0
    rw [S2520Psi_eq, Polynomial.aeval_map_algebraMap,
      Polynomial.aeval_algHom_apply S2510Embedding x.1 S2057Psi5F, hx, map_zero]⟩


/-- The root map is injective. -/
theorem S2520RootMap_injective : Function.Injective S2520RootMap := by
  intro x y h
  apply Subtype.ext
  apply S2510Embedding_injective
  exact congrArg Subtype.val h

/-- The two root types have the same cardinality (both 12). -/
theorem S2520Root_card_eq : Fintype.card S2132DivisionRoots = Fintype.card S2056Root := by
  rw [S2132DivisionRoots_card, ← Nat.card_eq_fintype_card, S2056Root_card]

/-- The embedding identifies the splitting-field roots with the closure roots. -/
noncomputable def S2520RootEquiv : S2132DivisionRoots ≃ S2056Root :=
  Equiv.ofBijective S2520RootMap
    (Fintype.bijective_iff_injective_and_card S2520RootMap |>.mpr
      ⟨S2520RootMap_injective, S2520Root_card_eq⟩)

@[simp] theorem S2520RootEquiv_apply (x : S2132DivisionRoots) :
    S2520RootEquiv x = S2520RootMap x := rfl

/-- The root identification intertwines the splitting-field action with the
absolute Galois action. -/
theorem S2520RootMap_comm
    (tau : S2132L ≃ₐ[S1720Field] S2132L)
    (sigma : S1725AbsoluteGalois)
    (hsigma : ∀ x : S2132L, sigma (S2510Embedding x) = S2510Embedding (tau x))
    (x : S2132DivisionRoots) :
    S2520RootMap (S2132DivisionRootEquiv tau x) =
      S2501RootPerm sigma (S2520RootMap x) := by
  apply Subtype.ext
  change S2510Embedding (tau x.1) = sigma (S2510Embedding x.1)
  exact (hsigma x.1).symm

/-- The root permutations have the same cycle type. -/
theorem S2520cycleType_eq
    (tau : S2132L ≃ₐ[S1720Field] S2132L)
    (sigma : S1725AbsoluteGalois)
    (hsigma : ∀ x : S2132L, sigma (S2510Embedding x) = S2510Embedding (tau x)) :
    Equiv.Perm.cycleType (S2132DivisionRootEquiv tau) =
      (S2501RootPerm sigma).cycleType := by
  have hperm : S2520RootEquiv.permCongr (S2132DivisionRootEquiv tau) =
      S2501RootPerm sigma := by
    apply Equiv.ext
    intro x
    rw [Equiv.permCongr_apply]
    have h := S2520RootMap_comm tau sigma hsigma (S2520RootEquiv.symm x)
    have hx : S2520RootMap (S2520RootEquiv.symm x) = x :=
      S2520RootEquiv.apply_symm_apply x
    simpa [hx] using h
  have hcycle := S2132cycleType_permCongr S2520RootEquiv
    (S2132DivisionRootEquiv tau)
  rw [hperm] at hcycle
  exact hcycle.symm

/-- **The exact missing transfer is actual.** -/
theorem S2520RootCycleTransferRequired : S2501RootCycleTransferRequired := by
  intro tau
  obtain ⟨sigma, hsigma⟩ := S2510_exists_lift tau
  refine ⟨sigma, ?_⟩
  exact (S2520cycleType_eq tau sigma hsigma).symm

/-- Consequently the S2132 target implies S2480FirstMissing. -/
theorem S2520S2132ToFirstMissingRequired : S2501S2132ToFirstMissingRequired :=
  S2501S2132ToFirstMissing_of_rootTransfer
    (S2501RootTransfer_of_transfer S2520RootCycleTransferRequired)

/-- The S2132 honest target gives S2480FirstMissing. -/
theorem S2520S2480FirstMissing_of_S2132
    (h : S2132FrobInducesPairCycleType) : S2480FirstMissing :=
  S2501S2480FirstMissing_of_S2132_and_transfer h S2520RootCycleTransferRequired

end LeanFormal.IUT.XiFPaper.S2520RootCycleTransferActual

end
