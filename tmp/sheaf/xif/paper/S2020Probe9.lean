import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
import tmp.sheaf.xif.paper.S2014DicksonClassificationActual
open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

lemma le_normalizer_map_of_normal {G : Type*} [Group G] (H : Subgroup G) (K : Subgroup H)
    [K.Normal] : H ≤ Subgroup.normalizer (K.map H.subtype : Set G) := by
  intro h hh
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    have hk' : (⟨h, hh⟩ : H) * k * (⟨h, hh⟩ : H)⁻¹ ∈ K :=
      Subgroup.Normal.conj_mem (inferInstance : K.Normal) k hk ⟨h, hh⟩
    exact Subgroup.mem_map.mpr ⟨_, hk', by simp [mul_assoc]⟩
  · intro hy
    obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.mp hy
    have hk' : (⟨h, hh⟩ : H)⁻¹ * k * (⟨h, hh⟩ : H) ∈ K := by
      simpa using Subgroup.Normal.conj_mem (inferInstance : K.Normal) k hk (⟨h, hh⟩ : H)⁻¹
    refine Subgroup.mem_map.mpr ⟨_, hk', ?_⟩
    change H.subtype ((⟨h, hh⟩ : H)⁻¹ * k * (⟨h, hh⟩ : H)) = y
    rw [show H.subtype ((⟨h, hh⟩ : H)⁻¹ * k * (⟨h, hh⟩ : H))
        = h⁻¹ * ((k : H) : G) * h by simp [mul_assoc]]
    rw [show ((k : H) : G) = H.subtype k from rfl]
    rw [hk_eq]
    group

lemma factorization_six_three : Nat.factorization 6 3 = 1 := by
  have hmem : 3 ∈ (3 : ℕ).primeFactorsList := by
    rw [Nat.mem_primeFactorsList (by norm_num)]
    exact ⟨by norm_num, dvd_rfl⟩
  rw [show 6 = 2 * 3 by norm_num]
  rw [Nat.factorization_eq_of_coprime_right (by norm_num : Nat.Coprime 2 3) hmem]
  exact Nat.Prime.factorization_self (by norm_num)

lemma exists_normal_three_of_card24 (H : Subgroup GL2) (hcard : Nat.card H = 24)
    (hdet : DetSurjectiveOn H) :
    ∃ P : Subgroup GL2, Nat.card P = 3 ∧
      H ≤ Subgroup.normalizer (P : Set GL2) := by
  letI : Fintype H := Fintype.ofFinite H
  let f : H →* K5ˣ := (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).comp H.subtype
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨h, hh, hhd⟩ := hdet a
    exact ⟨⟨h, hh⟩, hhd⟩
  let K : Subgroup H := f.ker
  have hidx : K.index = 4 := by
    dsimp [K]
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    decide
  have hKcard : Nat.card K = 6 := by
    have hmul := Subgroup.index_mul_card (H := K)
    rw [hidx, hcard] at hmul
    omega
  letI : Fintype K := Fintype.ofFinite K
  let P : Sylow 3 K := default
  have hPcard : Nat.card P = 3 := by
    rw [Sylow.card_eq_multiplicity, hKcard, factorization_six_three]
    norm_num
  haveI : Finite (Sylow 3 K) := Sylow.finite_of_finiteIndex P
  have hPchar : P.Characteristic := by
    have hnorm : P.Normal := by
      have hidx2 : P.index = 2 := by
        have hmul := Subgroup.index_mul_card (H := (P : Subgroup K))
        rw [hPcard, hKcard] at hmul
        omega
      exact Subgroup.normal_of_index_eq_two hidx2
    exact Sylow.characteristic_of_normal P hnorm
  let PH : Subgroup H := P.map K.subtype
  have hPHnormal : PH.Normal := inferInstance
  have hPHcard : Nat.card PH = 3 := by
    dsimp [PH]
    rw [Subgroup.card_map_of_injective K.subtype_injective, hPcard]
  refine ⟨PH.map H.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hPHcard]
  · exact le_normalizer_map_of_normal H PH

end LeanFormal.IUT.XiFPaper.S2009DicksonActual
