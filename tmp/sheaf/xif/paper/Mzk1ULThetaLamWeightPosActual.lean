/- hM 局部权重口径（Lead 裁决）：Qloc b := Qb b / thetaLamWeight b,
  thetaLamWeight b * Qloc b = Qb b（thetaLamWeight≠0）。
  donor: Mzk1URThetaKSideActual.thetaLamWeight/lamWeight/dModF/lamWeight_nonneg/dModF_pos（DONE 23:55:17）;
  Mzk1ULQbVecActual.Qb（DONE 12:47:05）。 -/
import tmp.sheaf.xif.paper.Mzk1ULQbVecActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULThetaLamWeightPosActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- lamWeight b = [Fmod_b:Q_p] > 0。 -/
theorem lamWeight_pos (b : Bad (nativePlaceSelection T)) : 0 < lamWeight T b := by
  unfold lamWeight
  haveI : Fact (Nat.Prime ((completionRationalPrime b.1).val)) := completionRationalPrime_fact b.1
  exact_mod_cast (Module.finrank_pos (R := ℚ_[(completionRationalPrime b.1).val]) (M := NormalizedCompletion b.1))

/-- thetaLamWeight b = lamWeight b/d_mod > 0。 -/
theorem thetaLamWeight_pos (b : Bad (nativePlaceSelection T)) : 0 < thetaLamWeight T b := by
  unfold thetaLamWeight
  exact div_pos (lamWeight_pos T b) (dModF_pos T)

/-- 局部 Q（gen hM 用）：Qloc b = Qb b / thetaLamWeight b。 -/
noncomputable def Qloc (b : Bad (nativePlaceSelection T)) : ℝ :=
  Qb (T := T) b / thetaLamWeight T b

/-- thetaLamWeight b * Qloc b = Qb b。 -/
theorem thetaLamWeight_mul_Qloc (b : Bad (nativePlaceSelection T)) :
    thetaLamWeight T b * Qloc (T := T) b = Qb (T := T) b := by
  unfold Qloc
  have hw : thetaLamWeight T b ≠ 0 := ne_of_gt (thetaLamWeight_pos T b)
  field_simp

#print axioms lamWeight_pos
#print axioms thetaLamWeight_pos
#print axioms thetaLamWeight_mul_Qloc

end LeanFormal.IUT.XiFPaper.Mzk1ULThetaLamWeightPosActual
