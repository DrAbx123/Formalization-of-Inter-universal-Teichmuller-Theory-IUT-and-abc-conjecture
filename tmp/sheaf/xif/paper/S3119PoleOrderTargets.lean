import tmp.sheaf.xif.paper.S3119NormDegreeActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119YDecompositionActual
open LeanFormal.IUT.XiFPaper.S3119PhiMatrixActual
open LeanFormal.IUT.XiFPaper.S3119NormDegreeActual
namespace LeanFormal.IUT.XiFPaper.S3119PoleOrderTargets
set_option backward.isDefEq.respectTransparency false
variable {l : PrimeGeFive}

/-- φ x0 的 norm degree 保持为 4，等价于 ∞ pole order 2 保持。 -/
def S3119NormDegreeFourTarget (l : PrimeGeFive) : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l,
    (S3119Norm l (φ (S3119x0 (l := l)))).degree = 4

def S3119XqConstantTarget (l : PrimeGeFive) : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l,
    (S3119Xq l φ).degree ≤ 0

def S3119XpDegreeTwoTarget (l : PrimeGeFive) : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l,
    (S3119Xp l φ).degree = 2

#check S3119NormDegreeFourTarget
#check S3119XqConstantTarget
#check S3119XpDegreeTwoTarget
end LeanFormal.IUT.XiFPaper.S3119PoleOrderTargets
end
