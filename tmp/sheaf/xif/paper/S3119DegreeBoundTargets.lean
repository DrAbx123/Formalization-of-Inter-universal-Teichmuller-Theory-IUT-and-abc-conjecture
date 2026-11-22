import tmp.sheaf.xif.paper.S3119PhiMatrixActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119YDecompositionActual
open LeanFormal.IUT.XiFPaper.S3119PowReduceActual
open LeanFormal.IUT.XiFPaper.S3119PhiMatrixActual
namespace LeanFormal.IUT.XiFPaper.S3119DegreeBoundTargets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
variable {l : PrimeGeFive}

def S3119XqDegreeTarget (l : PrimeGeFive) : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l,
    (S3119Xq l φ).natDegree = 0

def S3119XpDegreeTarget (l : PrimeGeFive) : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l,
    (S3119Xp l φ).natDegree ≤ 1

#check S3119XqDegreeTarget
#check S3119XpDegreeTarget
end LeanFormal.IUT.XiFPaper.S3119DegreeBoundTargets
end
