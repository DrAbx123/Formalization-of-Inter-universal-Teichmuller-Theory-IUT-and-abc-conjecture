import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
noncomputable section
set_option maxHeartbeats 8000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2493UnitScalingActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
variable {K : Type} [Field K]
lemma rootSet_C_mul_unit (P : K[X]) {u : K} (hu : u ≠ 0) :
    (C u * P).rootSet K = P.rootSet K := by
  ext x
  rw [Polynomial.mem_rootSet, Polynomial.mem_rootSet]
  simp [eval_mul, hu]
lemma factorDegrees_C_mul_unit (P : K[X]) (hP : P ≠ 0) {u : K} (hu : u ≠ 0) :
    factorDegrees (C u * P) = factorDegrees P := by
  classical
  letI : DecidableEq K := Classical.decEq K
  unfold factorDegrees
  rw [UniqueFactorizationMonoid.normalizedFactors_mul (by simpa using (Polynomial.C_ne_zero.mpr hu)) hP]
  rw [UniqueFactorizationMonoid.normalizedFactors_of_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu))]
  rw [Multiset.zero_add]
#print axioms rootSet_C_mul_unit
#print axioms factorDegrees_C_mul_unit
end LeanFormal.IUT.XiFPaper.S2493UnitScalingActual
end
