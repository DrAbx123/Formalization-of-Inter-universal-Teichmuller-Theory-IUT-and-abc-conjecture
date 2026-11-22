import tmp.sheaf.xif.paper.S2055DicksonClassActual
import tmp.sheaf.xif.paper.S2294QE5DegreeValueActual
import tmp.sheaf.xif.paper.S2009DicksonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2298QE5OrderActual

open LeanFormal.IUT.XiFPaper.S2055DicksonClassActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S2294QE5DegreeValueActual

/-- Under determinant-surjective, twelve-pair transitive, and cycle-type
(10,2) hypotheses, the image subgroup is the whole GL2 and has order 480. -/
theorem S2298ImageCard_eq_480_of_hypotheses
    (H : Subgroup GL2) (hdet : DetSurjectiveOn H) (htrans : PairTransitive H)
    (h102 : HasCycleType102 H) :
    Nat.card H = 480 := by
  rw [S2055LargeImage_of_dickson H hdet htrans h102]
  have h : Nat.card ↥(⊤ : Subgroup GL2) = Nat.card GL2 :=
    Nat.card_congr (Subgroup.topEquiv (G := GL2)).toEquiv
  exact h.trans natCard_GL2

/-- From the Dickson transitive classification (without cycle type), a proper
det-surjective pair-transitive subgroup has order dividing 96 or 48. -/
theorem S2298ImageCard_dvd_96_or_48_of_dickson
    (hD : S2009DicksonTransitiveClassification)
    (H : Subgroup GL2) (hdet : DetSurjectiveOn H) (htrans : PairTransitive H)
    (hne : H ≠ ⊤) :
    Nat.card H ∣ 96 ∨ Nat.card H ∣ 48 := by
  rcases hD H hdet htrans hne with ⟨K, hHK, hK⟩ | ⟨K, hHK, hK⟩
  · left
    exact (Subgroup.card_dvd_of_le hHK).trans (by rw [hK])
  · right
    exact (Subgroup.card_dvd_of_le hHK).trans (by rw [hK])

/-- The degree of the actual Q(E[5]) splitting field is bounded by the
factorial 12 (actual S2294 input). -/
theorem S2298QE5Degree_dvd_factorial :
    Module.finrank ℚ s2289QE5 ∣ Nat.factorial 12 :=
  s2294QE5_finrank_dvd_factorial

/-- Exact first missing: the identification of the Q(E[5]) degree with the
order of the actual mod-5 image subgroup. -/
def S2298QE5DegreeEqualsImageOrderRequired
    (H : Subgroup GL2) : Prop :=
  Module.finrank ℚ s2289QE5 = Nat.card H

/-- Conditional degree computation: under the image hypotheses and the exact
degree/image-order identification, the Q(E[5]) degree is 480. -/
theorem S2298QE5Degree_eq_480_of_hypotheses
    (H : Subgroup GL2) (hdet : DetSurjectiveOn H) (htrans : PairTransitive H)
    (h102 : HasCycleType102 H)
    (hdeg : S2298QE5DegreeEqualsImageOrderRequired H) :
    Module.finrank ℚ s2289QE5 = 480 := by
  rw [hdeg, S2298ImageCard_eq_480_of_hypotheses H hdet htrans h102]

end LeanFormal.IUT.XiFPaper.S2298QE5OrderActual

end
