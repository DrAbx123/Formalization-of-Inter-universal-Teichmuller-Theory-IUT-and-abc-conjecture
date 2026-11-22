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

lemma normalizer_card_of_subgroup_three (hmain : S2014NormalizerCard) (P : Subgroup GL2)
    (hP : Nat.card P = 3) :
    Nat.card (Subgroup.normalizer (P : Set GL2)) = 48 := by
  letI : Fintype P := Fintype.ofFinite P
  have hdvd : 3 ∣ Nat.card P := by rw [hP]
  have hdvd' : 3 ∣ Fintype.card P := by simpa [Nat.card_eq_fintype_card] using hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hdvd'
  have hzle : Subgroup.zpowers ((g : P) : GL2) ≤ P := by
    rw [Subgroup.zpowers_le]
    exact g.2
  have hzcard : Nat.card (Subgroup.zpowers ((g : P) : GL2)) = 3 := by
    rw [Nat.card_zpowers]
    simpa using hg
  have hzmem : (Subgroup.zpowers ((g : P) : GL2) : Subgroup GL2) = P := by
    apply Subgroup.eq_of_le_of_card_ge hzle
    rw [hP, hzcard]
  rw [← hzmem]
  exact hmain (g : GL2) (by simpa using hg)

end LeanFormal.IUT.XiFPaper.S2009DicksonActual
