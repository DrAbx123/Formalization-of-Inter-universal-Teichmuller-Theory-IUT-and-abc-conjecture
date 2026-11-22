import tmp.sheaf.xif.paper.S3057GluingUniquenessActual
import tmp.sheaf.xif.paper.S2853E37NegationAutomorphismActual
import tmp.sheaf.xif.paper.S2857GlobalAlphaActual
import tmp.sheaf.xif.paper.S2857GlobalAlphaCompatActual
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S3057GluingUniquenessActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3060GluingDataFromChartYActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev R0 := S3030AffineOriginClassification.R0

def S3060ChartYBranches : Prop :=
  (forall (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (r : S3054ChartZRestriction β),
      r.φ.toRingHom = RingHom.id S3054ProjectiveTransport.R0 →
      S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ β.left =
        S2820E37ChartYMap S2844D6F6BaseChangeActual.K) ∧
  (forall (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (r : S3054ChartZRestriction β),
      r.φ.toRingHom = S2853RingHom S2844D6F6BaseChangeActual.K →
      S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ β.left =
        S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left)

theorem S3060_spec_alpha :
    Spec.map (CommRingCat.ofHom (S2853RingHom S2844D6F6BaseChangeActual.K)) =
      S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K := rfl

theorem S3060_chartZ_alpha :
    S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left =
      S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K ≫
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K := by
  have hf : S2820E37ChartZMap S2844D6F6BaseChangeActual.K =
      (E37ProjGlueData S2844D6F6BaseChangeActual.K
        (S2820E37TransitionIso S2844D6F6BaseChangeActual.K)).openCover.f
        (ULift.up false) := rfl
  have hg : alphaOverS2844.left =
      (E37ProjGlueData S2844D6F6BaseChangeActual.K
        (S2820E37TransitionIso S2844D6F6BaseChangeActual.K)).openCover.glueMorphisms
        (globalAlphaComp S2844D6F6BaseChangeActual.K)
        (globalAlphaCompat S2844D6F6BaseChangeActual.K) := rfl
  rw [hf, hg]
  have hglue :=
    (E37ProjGlueData S2844D6F6BaseChangeActual.K
      (S2820E37TransitionIso S2844D6F6BaseChangeActual.K)).openCover.ι_glueMorphisms
      (globalAlphaComp S2844D6F6BaseChangeActual.K)
      (globalAlphaCompat S2844D6F6BaseChangeActual.K) (ULift.up false)
  rw [show globalAlphaComp S2844D6F6BaseChangeActual.K (ULift.up false) =
      S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K ≫
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K from rfl] at hglue
  rw [← hf]
  exact hglue

theorem S3060_gluingData_of_chartY
    (hY : S3060ChartYBranches) : S3054GluingData := by
  intro β r0
  constructor
  · intro r hid
    have hZ : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫
          Over.Hom.left (𝟙 S2844D6F6BaseChangeActual.S2844X) := by
      rw [r.hsquare, hid]
      rw [Category.comp_id]
    have hYcomp : S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ β.left =
        S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫
          Over.Hom.left (𝟙 S2844D6F6BaseChangeActual.S2844X) := by
      rw [Category.comp_id]
      exact hY.1 β r hid
    exact S3057_gluingUniqueness β (𝟙 _) hZ hYcomp
  · intro r halpha
    have hspec : Spec.map (CommRingCat.ofHom r.φ.toRingHom) =
        Spec.map (CommRingCat.ofHom (S2853RingHom S2844D6F6BaseChangeActual.K)) :=
      congrArg (fun f : S3054ProjectiveTransport.R0 →+* S3054ProjectiveTransport.R0 =>
        Spec.map (CommRingCat.ofHom f)) halpha
    have hZ1 : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
        Spec.map (CommRingCat.ofHom (S2853RingHom S2844D6F6BaseChangeActual.K)) ≫
          S2820E37ChartZMap S2844D6F6BaseChangeActual.K := by
      exact r.hsquare.trans (congrArg (fun z => z ≫ S2820E37ChartZMap S2844D6F6BaseChangeActual.K) hspec)
    have hZ : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left := by
      have hA : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
          S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K ≫
            S2820E37ChartZMap S2844D6F6BaseChangeActual.K :=
        hZ1.trans (congrArg (fun z => z ≫ S2820E37ChartZMap S2844D6F6BaseChangeActual.K)
          S3060_spec_alpha)
      exact hA.trans S3060_chartZ_alpha.symm
    have hYcomp : S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ β.left =
        S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left :=
      hY.2 β r halpha
    exact S3057_gluingUniqueness β alphaOverS2844 hZ hYcomp

#check S3060ChartYBranches
#check S3060_gluingData_of_chartY
#print axioms S3060_gluingData_of_chartY

end LeanFormal.IUT.XiFPaper.S3060GluingDataFromChartYActual
end