import tmp.sheaf.xif.paper.S2464D5CorrectedActual
import tmp.sheaf.xif.paper.S2460D5CloseActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2460D5CloseActual
open LeanFormal.IUT.XiFPaper.S2464D5CorrectedActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
attribute [local instance] Ideal.Quotient.field
namespace LeanFormal.IUT.XiFPaper.S2465D5OrbitSizeActual
lemma s2465_filter_ne_one_add_replicate_count_one (M : Multiset Nat) :
    M.filter (fun n => n ≠ 1) + Multiset.replicate (M.count 1) 1 = M := by
  classical
  ext n
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases hn : n = 1
  · subst hn; simp
  · have h1n : ¬ (1 = n) := fun h => hn h.symm
    simp [hn, h1n]
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp K L
local instance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp K L
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
local instance : DecidableEq ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L) := Classical.decEq _
include hp hP hPover hmonic hsep hsplit in
lemma s2465_factorDegrees_sum :
    (factorDegrees (fbar f p)).sum = f.natDegree := by
  classical
  have hmonicbar : (fbar f p).Monic := s2397Fbar_monic f p P hmonic
  have hprod : (UniqueFactorizationMonoid.normalizedFactors (fbar f p)).prod = fbar f p := by
    have h := Polynomial.leadingCoeff_mul_prod_normalizedFactors (fbar f p)
    rw [hmonicbar.leadingCoeff, map_one, one_mul] at h
    exact h
  unfold factorDegrees
  rw [← Polynomial.natDegree_multiset_prod_of_monic]
  · rw [hprod]
    exact Polynomial.Monic.natDegree_map hmonic (Ideal.Quotient.mk p)
  · intro g hg
    exact ((Polynomial.mem_normalizedFactors_iff (s2397Fbar_ne_zero f p P hmonic)).mp hg).2.1
include hp hP hPover hmonic hsep hsplit in
theorem s2465_orbitSizeMultiset_rootPerm_eq_factorDegrees
    (sigma : Gal(L/K)) (Hglobal : IsArithFrobAt (RingOfIntegers K) sigma P) :
    orbitSizeMultiset (rootPerm K L f hsplit sigma) = factorDegrees (fbar f p) := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  have H2440 : IsArithFrobAt (RingOfIntegers K) sigma P := Hglobal
  have hcyc : (rootPerm K L f hsplit sigma).cycleType =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
    simpa [rootCycleType] using
      s2460RootCycleType_factorDegrees K L f p P hmonic hsep hsplit sigma H2440
  have hcardK : Fintype.card ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L) =
      f.natDegree := by
    rw [← Fintype.card_congr (s2440RootSetEquiv (K := K) (L := L) f hmonic)]
    exact card_rootSet_eq f p P hmonic hsep hsplit
  have hsum := s2465_factorDegrees_sum K L f p P hmonic hsep hsplit
  have hcount : (factorDegrees (fbar f p)).count 1 =
      f.natDegree - ((factorDegrees (fbar f p)).filter (fun n => n ≠ 1)).sum := by
    have hid := s2465_filter_ne_one_add_replicate_count_one (factorDegrees (fbar f p))
    have hsumid : ((factorDegrees (fbar f p)).filter (fun n => n ≠ 1)).sum +
        (factorDegrees (fbar f p)).count 1 = f.natDegree := by
      have h := congrArg Multiset.sum hid
      rw [Multiset.sum_add, Multiset.sum_replicate, hsum] at h
      simpa using h
    omega
  unfold orbitSizeMultiset
  rw [Equiv.Perm.card_fixedPoints]
  rw [hcyc, hcardK, ← hcount]
  exact s2465_filter_ne_one_add_replicate_count_one (factorDegrees (fbar f p))

include hp hP hPover hmonic hsep hsplit in
theorem s2465OrbitSizeStatement :
    DedekindFrobeniusOrbitSizeStatement f p P hmonic hsep hsplit := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  haveI : Finite ((RingOfIntegers L) ⧸ P) := inferInstance
  unfold DedekindFrobeniusOrbitSizeStatement
  obtain ⟨sigma, H⟩ := S2167FrobeniusExists K L P
  have Hloc : IsArithFrobAt (RingOfIntegers K) sigma P :=
    (LeanFormal.IUT.XiFPaper.S2463ActionTransportActual.s2463_isArithFrobAt_iff (K:=K) (L:=L) sigma P).mpr H
  exact ⟨sigma, H, s2465_orbitSizeMultiset_rootPerm_eq_factorDegrees K L f p P hmonic hsep hsplit sigma Hloc⟩

theorem s2465DedekindFrobeniusOrbitSizeTheorem : DedekindFrobeniusOrbitSizeTheorem := by
  intro K L _ _ _ _ _ _ _ f p hp P hP hPover hmonic hsep hsplit
  haveI : p.IsMaximal := hp
  haveI : P.IsPrime := hP
  haveI : P.LiesOver p := hPover
  exact s2465OrbitSizeStatement K L f p P hmonic hsep hsplit

theorem s2465S2217Missing : S2217Missing := s2465DedekindFrobeniusOrbitSizeTheorem
#print axioms s2465DedekindFrobeniusOrbitSizeTheorem
#print axioms s2465S2217Missing

#print axioms s2465OrbitSizeStatement

#print axioms s2465_factorDegrees_sum
#print axioms s2465_orbitSizeMultiset_rootPerm_eq_factorDegrees
end LeanFormal.IUT.XiFPaper.S2465D5OrbitSizeActual
end
