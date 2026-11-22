import tmp.sheaf.xif.paper.S3119PhiMatrixActual
import tmp.sheaf.xif.paper.S3119PowReduceDegreeActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119YDecompositionActual
open LeanFormal.IUT.XiFPaper.S3119PowReduceActual
open LeanFormal.IUT.XiFPaper.S3119PhiMatrixActual
open LeanFormal.IUT.XiFPaper.S3119PowReduceDegreeActual
namespace LeanFormal.IUT.XiFPaper.S3119PhiDegreeActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
variable {l : PrimeGeFive}

lemma S3119PhiP_degree_bound (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) :
    (S3119PhiP l φ p).natDegree ≤
      p.natDegree * S3119M l (S3119Xp l φ) (S3119Xq l φ) :=
  S3119PolyP_degree_bound (l := l) (S3119Xp l φ) (S3119Xq l φ) p

lemma S3119PhiQ_degree_bound (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) :
    (S3119PhiQ l φ p).natDegree ≤
      p.natDegree * S3119M l (S3119Xp l φ) (S3119Xq l φ) :=
  S3119PolyQ_degree_bound (l := l) (S3119Xp l φ) (S3119Xq l φ) p

#check S3119PhiP_degree_bound
#check S3119PhiQ_degree_bound
#print axioms S3119PhiP_degree_bound
end LeanFormal.IUT.XiFPaper.S3119PhiDegreeActual
end
