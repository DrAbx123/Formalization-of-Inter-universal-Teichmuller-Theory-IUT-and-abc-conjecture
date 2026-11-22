import tmp.sheaf.xif.paper.S3119EvalPointInjectiveActual
import tmp.sheaf.xif.paper.S3119ProjectiveInfinityActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1331OrbicurveClauseAudit
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119EvalPointInjectiveActual
open LeanFormal.IUT.XiFPaper.S3119ProjectiveInfinityActual
namespace LeanFormal.IUT.XiFPaper.S3119EvalPointActionActual
set_option backward.isDefEq.respectTransparency false
variable {l : PrimeGeFive}

/-- The projective point action induced by an affine coordinate-ring
automorphism: fix infinity, and on a nonzero projective point choose an affine
K-point evaluating to it and precompose with φ.  Well-definedness is
S1348EvalPoint_injective. -/
noncomputable def S3119Sigma
    (φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l)
    (P : (S1348Curve l).toProjective.Point) :
    (S1348Curve l).toProjective.Point := by
  classical
  exact if h : P = 0 then 0
  else
    S1348EvalPoint l
      ((Classical.choose (S1348PointAlgHom_surjective l
        ⟨P, by rw [S1331_puncture_eq_zero]; exact h⟩)).comp φ.toAlgHom)


theorem S3119Sigma_zero
    (φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l) :
    S3119Sigma φ (S3119InfinityPoint (l := l)) = S3119InfinityPoint (l := l) := by
  simp only [S3119Sigma, S3119InfinityPoint]
  split_ifs with h
  · rfl
  · exfalso
    exact h trivial

theorem S3119Sigma_affine
    (φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l)
    (ψ : S1348CoordinateRing l →ₐ[S1348K l] S1348K l) :
    S3119Sigma φ (S1348EvalPoint l ψ) =
      S1348EvalPoint l (ψ.comp φ.toAlgHom) := by
  have hne : S1348EvalPoint l ψ ≠ 0 := S1348EvalPoint_ne_zero l ψ
  simp only [S3119Sigma]
  rw [dif_neg hne]
  let ψch : S1348CoordinateRing l →ₐ[S1348K l] S1348K l :=
    Classical.choose (S1348PointAlgHom_surjective l
      (⟨S1348EvalPoint l ψ, by rw [S1331_puncture_eq_zero]; exact hne⟩ :
        S1331ClausePuncturedCurve l))
  have hspec : S1348EvalPunctured l ψch =
      (⟨S1348EvalPoint l ψ, by rw [S1331_puncture_eq_zero]; exact hne⟩ :
        S1331ClausePuncturedCurve l) :=
    Classical.choose_spec (S1348PointAlgHom_surjective l
      (⟨S1348EvalPoint l ψ, by rw [S1331_puncture_eq_zero]; exact hne⟩ :
        S1331ClausePuncturedCurve l))
  have hEval : S1348EvalPoint l ψch = S1348EvalPoint l ψ := by
    have := congrArg Subtype.val hspec
    simpa [S1348EvalPunctured] using this
  have hψch : ψch = ψ := S1348EvalPoint_injective hEval
  change S1348EvalPoint l (ψch.comp φ.toAlgHom) =
    S1348EvalPoint l (ψ.comp φ.toAlgHom)
  rw [hψch]

theorem S3119ProjectivePointActionTarget_proof :
    S3119ProjectivePointActionTarget (l := l) := by
  intro φ
  exact ⟨S3119Sigma φ, S3119Sigma_zero φ, S3119Sigma_affine φ⟩

#check S3119Sigma_zero
#check S3119Sigma_affine
#check S3119ProjectivePointActionTarget_proof
#print axioms S3119ProjectivePointActionTarget_proof

#check S3119Sigma
end LeanFormal.IUT.XiFPaper.S3119EvalPointActionActual
end
