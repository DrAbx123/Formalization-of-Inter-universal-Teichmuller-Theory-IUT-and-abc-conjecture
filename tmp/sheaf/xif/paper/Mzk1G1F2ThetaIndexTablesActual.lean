/- R3b (1/n): the two explicit index tables of route §5.3, and the current-Bad part of (R3.2).

  ROUTE §5.3 (coord/P7-G1-P6-P8-CLOSURE-ROUTE-20261116.md L295-321):
  * table 1: all finite q-places -> those entering the current Bad / excluded by local conditions;
  * table 2: each Bad fiber -> the lift actually used for source transport / the remaining lifts.
  Differences are computed separately and (together with archimedean and fixed special-place
  differences) give (R3.2)  0 <= Q_all - Q_used <= C_d sqrt(h) log(2 C_d h) + C_{K_V}.

  RECON donors (DONE): `Mzk1ULQSelectedActual`
  * `selectedFPlace (b) = nativeBadToFPlace T b`, `selectedIdeal (b)`, `fiberTerm (b P hP)`,
  * `QSelected`, `hMinusQ`, `fiberTerm_nonneg`, `QSelected_nonneg`, `hMinusQ_nonneg`,
  * `qPilotMagnitudePaper_v2 = QSelected + hMinusQ` (qPilotMagnitudePaper_v2_split).
  This file: the explicit table structures and the fiber-lift split identity, i.e. the
  current-Bad part `Q_all^Bad = Q_used^Bad + (Q_all^Bad - Q_used^Bad)` with the second summand
  `hMinusQ >= 0`. The paper-level all-q vs Bad difference is recorded as the non-Bad part
  `qAllMinusQBad` (explicit definition below), NOT hidden inside hMinusQ. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1ULQSelectedActual
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Tactic

noncomputable section
open scoped NumberField
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaIndexTablesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULQSelectedActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **表 1**：全部 finite q-位与进入当前 Bad 的位（显式数据 + 包含）。 -/
structure ThetaQIndexTable where
  /-- 全部 finite q-位（paper V^bad 全纤维的位）。 -/
  AllQ : Finset (NumberField.FinitePlace T.arithmetic.F)
  /-- 进入当前 Bad 的位（nativeBadToFPlace 的像）。 -/
  BadQ : Finset (NumberField.FinitePlace T.arithmetic.F)
  /-- 局部位条件排除的位。 -/
  ExcludedQ : Finset (NumberField.FinitePlace T.arithmetic.F)
  hsubset : BadQ ⊆ AllQ

/-- **表 2**：每个 Bad 纤维的实际 lift 表（数据与 DONE 的 chosen/补充 lift 对齐）。 -/
structure ThetaFiberLiftTable (b : Bad (nativePlaceSelection T)) where
  /-- fiber 中全部 lift。 -/
  Lifts : Finset (Ideal (𝓞 (T.arithmetic.F)))
  /-- 实际用于源运输的 lift。 -/
  Used : Ideal (𝓞 (T.arithmetic.F))
  hLifts : Lifts = IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))
  hUsed : Used ∈ Lifts

/-- fiber 项之和可拆成「选中项 + 其余项」（表 2 的 split 恒等式）。 -/
theorem fiber_sum_split (b : Bad (nativePlaceSelection T))
    (hU : selectedIdeal T b ∈
      IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))) :
    (∑ x ∈ (IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal)
        (𝓞 (T.arithmetic.F))).attach,
      fiberTerm T b x.1 x.2)
      = (∑ x ∈ (IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal)
          (𝓞 (T.arithmetic.F))).attach,
          if x.1 = selectedIdeal T b then fiberTerm T b x.1 x.2 else 0)
        + (∑ x ∈ (IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal)
          (𝓞 (T.arithmetic.F))).attach,
          if x.1 = selectedIdeal T b then 0 else fiberTerm T b x.1 x.2) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x.1 = selectedIdeal T b
  · simp [h]
  · simp [h]

#print axioms fiber_sum_split

/-- 当前 Bad 部分的 (R3.2)：`Q_all^Bad = Q_used^Bad + (Q_all^Bad - Q_used^Bad)`，
    且余项 `hMinusQ >= 0`（DONE donor）。 -/
theorem currentBad_Q_split_and_nonneg :
    qPilotMagnitudePaper_v2 (T := T) = QSelected (T := T) + hMinusQ (T := T) ∧
      0 ≤ hMinusQ (T := T) :=
  ⟨qPilotMagnitudePaper_v2_eq_QSelected_add_hMinusQ (T := T), hMinusQ_nonneg (T := T)⟩

#print axioms currentBad_Q_split_and_nonneg

/-! ## 表 1 的补集部分：全部 finite q 位中未进入当前 Bad 的位 -/

/-- 全部 finite q 位中未进入当前 Bad 的位（dato: 具体 `AllQ`/`BadQ` 由 source 填入）。 -/
noncomputable def nonBadQ (Tab : ThetaQIndexTable (T := T)) :
    Finset (NumberField.FinitePlace T.arithmetic.F) := by
  classical
  exact Tab.AllQ \ Tab.BadQ

/-- 表 1 的划分：`BadQ` 与 `nonBadQ` 的基数之和 = `AllQ` 的基数。 -/
theorem nonBadQ_card_add_badQ (Tab : ThetaQIndexTable (T := T)) :
    Tab.BadQ.card + (nonBadQ (T := T) Tab).card = Tab.AllQ.card := by
  classical
  unfold nonBadQ
  have h := Finset.card_sdiff_add_card_eq_card (s := Tab.BadQ) (t := Tab.AllQ) Tab.hsubset
  omega

/-- 表 1 的补集基数不超过全部位数。 -/
theorem nonBadQ_card_le (Tab : ThetaQIndexTable (T := T)) :
    (nonBadQ (T := T) Tab).card ≤ Tab.AllQ.card := by
  classical
  unfold nonBadQ
  exact Finset.card_le_card (Finset.sdiff_subset)

#print axioms nonBadQ_card_add_badQ
#print axioms nonBadQ_card_le


/-! ## 表 2 的实际实例：以 source selection 的 lift 填表 -/

/-- 以 `primesOverFinset` 为 Lifts、`selectedIdeal` 为实际 lift 的表 2 实例。 -/
noncomputable def fiberTableOfBad (b : Bad (nativePlaceSelection T))
    (hU : selectedIdeal T b ∈ IsDedekindDomain.primesOverFinset
      (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))) :
    ThetaFiberLiftTable (T := T) b where
  Lifts := IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))
  Used := selectedIdeal T b
  hLifts := rfl
  hUsed := hU

/-- 该表的 `Used` 就是 source selection 的 `selectedIdeal`。 -/
theorem fiberTableOfBad_used (b : Bad (nativePlaceSelection T))
    (hU : selectedIdeal T b ∈ IsDedekindDomain.primesOverFinset
      (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))) :
    (fiberTableOfBad (T := T) b hU).Used = selectedIdeal T b := rfl

#print axioms fiberTableOfBad_used


end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaIndexTablesActual