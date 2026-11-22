import tmp.sheaf.xif.paper.S2653DedekindToRangeActual

noncomputable section
set_option maxHeartbeats 4000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2653DedekindToRangeActual
open LeanFormal.IUT.XiFPaper.S2643RootTransportFixActual
open LeanFormal.IUT.XiFPaper.S2642RootToRangeTransport
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

namespace LeanFormal.IUT.XiFPaper.S2655NonmonicRangeActual

theorem S2655_filter_ne_one_add_replicate_count_one (M : Multiset ℕ) :
    M.filter (fun n => n ≠ 1) + Multiset.replicate (M.count 1) 1 = M := by
  classical
  ext n
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases hn : n = 1
  · subst hn
    simp
  · have h1n : ¬ (1 = n) := fun h => hn h.symm
    simp [hn, h1n]

theorem S2655_cycleType_of_orbitSize
    {α : Type*} [Fintype α] (σ : Equiv.Perm α)
    (h : S2217DedekindFrobTheoremActual.orbitSizeMultiset σ =
      ({10, 2} : Multiset ℕ)) :
    @Equiv.Perm.cycleType α _ (Classical.decEq α) σ =
      ({10, 2} : Multiset ℕ) := by
  classical
  have hfilt_rep :
      (Multiset.replicate (Fintype.card (Function.fixedPoints σ)) 1).filter
        (fun x => x ≠ 1) = 0 := by
    induction Fintype.card (Function.fixedPoints σ) with
    | zero => simp
    | succ n ih => simp [Multiset.replicate_succ, ih]
  have hfilter : (σ.cycleType.filter (fun x => x ≠ 1)) =
      ({10, 2} : Multiset ℕ) := by
    have hc := congrArg (fun M : Multiset ℕ => M.filter (fun x => x ≠ 1)) h
    simp only [S2217DedekindFrobTheoremActual.orbitSizeMultiset,
      Multiset.filter_add, hfilt_rep, add_zero] at hc
    rw [show (Multiset.filter (fun x => x ≠ 1) ({10, 2} : Multiset ℕ)) =
        ({10, 2} : Multiset ℕ) from by decide] at hc
    exact hc
  have hcount1 : σ.cycleType.count 1 = 0 := by
    have hle : σ.cycleType ≤
        S2217DedekindFrobTheoremActual.orbitSizeMultiset σ :=
      Multiset.le_add_right _ _
    have hcnt : (S2217DedekindFrobTheoremActual.orbitSizeMultiset σ).count 1 = 0 := by
      rw [h]
      decide
    have := Multiset.count_le_of_le (1 : ℕ) hle
    rw [hcnt] at this
    exact Nat.eq_zero_of_le_zero this
  have hsplit := S2655_filter_ne_one_add_replicate_count_one σ.cycleType
  rw [hcount1, Multiset.replicate_zero, add_zero] at hsplit
  rw [← hsplit, hfilter]
theorem S2655RangeTransport
    (f : (RingOfIntegers S1720Field)[X])
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    {c : S1720Field} (hc : c ≠ 0)
    (hq : f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
      C c * S2057Psi5F)
    (hcyc : S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (rootPerm S1720Field S2057FiveDivisionField f hsplit σ) =
      ({10, 2} : Multiset ℕ)) :
    S2203RangeCycleTypeRequired S1982Basis := by
  classical
  letI : DecidableEq
      (↑((f.map (algebraMap (RingOfIntegers S1720Field)
        S1720Field)).rootSet S2057FiveDivisionField)) := Classical.decEq _
  have hcycle : (rootPerm S1720Field S2057FiveDivisionField f hsplit σ).cycleType =
      ({10, 2} : Multiset ℕ) :=
    S2655_cycleType_of_orbitSize _ hcyc
  have hperm : (S2653rootSetEquiv (K := S1720Field)
      (A := S2057FiveDivisionField) hc hq).permCongr
        (rootPerm S1720Field S2057FiveDivisionField f hsplit σ) =
      S2132DivisionRootEquiv σ :=
    S2653permCongr_rootPerm_eq_divisionRootEquiv f hsplit σ hc hq
  have hdiv : Equiv.Perm.cycleType (S2132DivisionRootEquiv σ) =
      ({10, 2} : Multiset ℕ) := by
    rw [← hperm, S2132cycleType_permCongr]
    exact hcycle
  obtain ⟨σ', hσ'⟩ := S2502cycleType_transport σ
  refine S2642RootMapToRangeTransport σ' ?_
  rw [← S2653S2480RootPerm_eq_S2642RootPerm σ', hσ', hdiv]

#check S2655RangeTransport
#print axioms S2655RangeTransport

end LeanFormal.IUT.XiFPaper.S2655NonmonicRangeActual
end
