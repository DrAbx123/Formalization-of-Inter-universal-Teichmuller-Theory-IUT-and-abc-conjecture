import tmp.sheaf.xif.paper.S3123LeftMapActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123LeftCoeActual
open LeanFormal.IUT.XiFPaper.S3123LeftExplicitActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapActual

namespace LeanFormal.IUT.XiFPaper.S3123LeftMapIdActual

variable {l : PrimeGeFive}

lemma S3123LeftId_eq
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (𝟙 (S3123LeftObj (l := l) U)) =
      (𝟙 ((S3123Left (l := l)).obj U)) := by
  cases S3123LeftObj_eq (l := l) U
  rfl

set_option maxHeartbeats 800000 in
noncomputable def S3123LeftMapId
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    S3123LeftMap (l := l) (𝟙 U) ≅ 𝟙 (S3123LeftObj (l := l) U) := by
  have h' : (S3123Left (l := l)).obj U = S3123LeftObj (l := l) U :=
    (S3123LeftObj_eq (l := l) U).symm
  let oldMap := (S3123Left (l := l)).map (𝟙 U)
  have hmapType :
      ((S3123Left (l := l)).obj U ⟶ (S3123Left (l := l)).obj U) =
        (S3123LeftObj (l := l) U ⟶ S3123LeftObj (l := l) U) :=
    congrArg₂ (fun (A B : Cat) => (A ⟶ B)) h' h'
  have hmapType_rfl : hmapType = rfl := Subsingleton.elim _ _
  have hmap : S3123LeftMap (l := l) (𝟙 U) = cast hmapType oldMap := rfl
  rw [hmap, hmapType_rfl]
  have hId : (𝟙 ((S3123Left (l := l)).obj U)) =
      𝟙 (S3123LeftObj (l := l) U) :=
    (S3123LeftId_eq (l := l) U).symm
  exact ((S3123Left (l := l)).mapId U).trans (eqToIso hId)

#check S3123LeftMapId

end LeanFormal.IUT.XiFPaper.S3123LeftMapIdActual
end
