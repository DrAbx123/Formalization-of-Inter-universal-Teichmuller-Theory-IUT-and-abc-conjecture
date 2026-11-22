import tmp.sheaf.xif.paper.EtTh10ThetaQuotientLawsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

/-!
# STEP 0 prior-art: theta realization|thetaPowerKernel|ellipticPowerKernel|power-kernel monotone|geometric realization -> hits LeanFormal/IUT/IUTII/Theta/EtaleThetaQuotient.lean:29-160 (thetaDerivedSubgroup/thetaCommutatorKernel/ThetaQuotient/EllipticAbelianization/power kernels/mod-l projections/thetaCenter) -> REUSE (class A: power-kernel monotonicity in the level l + projection surjectivity re-exports; realization deeper rows class-B named).

# [EtTh] 11: theta quotient/realization rows at the mod-l level (class A)

Corpus: papers/motizuki_corpus/text/The Etale Theta Function and its Frobenioid-theoretic
Manifestations.txt, theta-group quotient package and its geometric realization
(class-B here).
CLASS A (proved here): the power kernels are monotone in the level l (l1 | l2),
for both the theta quotient and the elliptic abelianization; the projection
surjectivity facts are re-exported.  CLASS B (named, NOT proved): the geometric
realization of the theta groups (profinite/etale), the Frobenioid-theoretic
manifestation, and the actual theta function transformation on the realized
object.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.EtTh11ThetaRealizationRowsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.EtTh10ThetaQuotientLawsActual

universe u

/-- The theta power kernels are ANTI-monotone in the level: l1 | l2 implies
thetaPowerKernel l2 <= thetaPowerKernel l1 (class A; l2-th powers are l1-th powers). -/
theorem etTh11_thetaPowerKernel_mono (G : Type u) [Group G] {l1 l2 : Nat}
    (h : l1 ∣ l2) :
    thetaPowerKernel G l2 ≤ thetaPowerKernel G l1 := by
  obtain ⟨k, hk⟩ := h
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨y, rfl⟩
  have h1 : y ^ l2 = (y ^ k) ^ l1 := by
    rw [hk, mul_comm l1 k, pow_mul]
  rw [h1]
  exact Subgroup.subset_normalClosure ⟨y ^ k, rfl⟩

/-- The elliptic power kernels are ANTI-monotone in the level (class A). -/
theorem etTh11_ellipticPowerKernel_mono (G : Type u) [Group G] {l1 l2 : Nat}
    (h : l1 ∣ l2) :
    ellipticPowerKernel G l2 ≤ ellipticPowerKernel G l1 := by
  obtain ⟨k, hk⟩ := h
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨y, rfl⟩
  have h1 : y ^ l2 = (y ^ k) ^ l1 := by
    rw [hk, mul_comm l1 k, pow_mul]
  rw [h1]
  exact Subgroup.subset_normalClosure ⟨y ^ k, rfl⟩

/-- The mod-l theta projection remains surjective (class A, reused). -/
theorem etTh11_modLThetaProjection_surjective (G : Type u) [Group G] (l : Nat) :
    Function.Surjective (modLThetaProjection G l) :=
  modLThetaProjection_surjective G l

/-- The mod-l theta-to-elliptic map remains surjective (class A, reused). -/
theorem etTh11_modLThetaToElliptic_surjective (G : Type u) [Group G] (l : Nat) :
    Function.Surjective (modLThetaToElliptic G l) :=
  modLThetaToElliptic_surjective G l

/-- Theta realization rows (class A proved vs class B named). -/
def etTh11Rows : List (String × String × String) :=
  [ ("theta power-kernel level anti-monotonicity", "A", "PROVED etTh11_thetaPowerKernel_mono (l1 | l2 => kernel l2 <= kernel l1)")
  , ("elliptic power-kernel level anti-monotonicity", "A", "PROVED etTh11_ellipticPowerKernel_mono")
  , ("mod-l projection surjectivity (theta / elliptic / theta-to-elliptic)", "A", "REUSED EtaleThetaQuotient:93-140 (re-exported)")
  , ("thetaCenter in the center of the theta quotient", "A", "REUSED EtaleThetaQuotient:142-150 (EtTh08 re-export)")
  , ("geometric realization of the theta groups (profinite/etale)", "B", "NAMED paper input; no realized object constructed here")
  , ("Frobenioid-theoretic manifestation of the theta function", "B", "NAMED; [EtTh] deep structure, interface only")
  , ("actual theta transformation on the realized object", "B", "NAMED; only ThetaShiftData EtTh08/09 formalized") ]

/-- The theta realization row record has seven rows. -/
theorem etTh11Rows_length : etTh11Rows.length = 7 := rfl

#check etTh11_thetaPowerKernel_mono
#check etTh11_ellipticPowerKernel_mono
#check etTh11_modLThetaToElliptic_surjective
#check etTh11Rows_length

end LeanFormal.IUT.XiFPaper.EtTh11ThetaRealizationRowsActual
end