import tmp.sheaf.xif.paper.S2982A6SourceDataActual
import tmp.sheaf.xif.paper.S2888OriginPreservingOrderTwo
import tmp.sheaf.xif.paper.S2877UniqueReductionAudit
import tmp.sheaf.xif.paper.S2858AlphaOverActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2982A6SourceDataActual
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3028OriginPreservingClassification

/-- Origin-preserving order-two classification: an origin-fixing order-two
automorphism is the identity or the chart alpha automorphism. -/
def S3028OriginPreservingClassification : Prop :=
  ∀ β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
    S2888OriginPreserving β →
      β = 𝟙 S2844D6F6BaseChangeActual.S2844X ∨ β = alphaOverS2844

/-- This is exactly the S2888 origin-preserving classification target. -/
theorem S3028_iff_S2888 :
    S3028OriginPreservingClassification ↔
      S2888OriginPreservingOrderTwoClassification :=
  Iff.rfl

/-- The id branch of the origin-preserving classification. -/
theorem S3028_id_mem :
    (𝟙 S2844D6F6BaseChangeActual.S2844X) =
        (𝟙 S2844D6F6BaseChangeActual.S2844X) ∨
      (𝟙 S2844D6F6BaseChangeActual.S2844X) = alphaOverS2844 :=
  Or.inl rfl

/-- The alpha branch of the origin-preserving classification, actual from
alpha-square and alpha being origin-preserving. -/
theorem S3028_alpha_mem
    (hα : S2888OriginPreserving alphaOverS2844) :
    alphaOverS2844 = 𝟙 S2844D6F6BaseChangeActual.S2844X ∨
      alphaOverS2844 = alphaOverS2844 :=
  Or.inr rfl

/-- The full (unrestricted) S2877 order-two classification is false as soon as
there is a nontrivial order-two translation which is neither id nor alpha.
This is the E37 rational 2-torsion translation phenomenon. -/
theorem S3028_full_classification_false_of_translation
    (τ : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hτ2 : τ ≫ τ = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hneid : τ ≠ 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hnealpha : τ ≠ alphaOverS2844) :
    ¬ S2877OrderTwoAutClassification := by
  intro h
  rcases h τ hτ2 with hid | halpha
  · exact hneid hid
  · exact hnealpha halpha

/-- The origin-preserving restriction rules out exactly the translation branch:
if the full classification holds then the origin-preserving classification
holds by specialization. -/
theorem S3028_origin_of_full
    (h : S2877OrderTwoAutClassification) :
    S3028OriginPreservingClassification := by
  intro β hβ _
  exact h β hβ

/-!
## First error / why the forward fix is the origin-preserving form

The unrestricted S2877OrderTwoAutClassification says every order-two
automorphism of S2844X is id or alphaOverS2844.  On the full E37 projective
scheme this is expected to be FALSE: rational 2-torsion translation
automorphisms are order two and are neither id nor alpha.  The actual
conditional refutation S3028_full_classification_false_of_translation records
exactly what would refute it.

The forward target S3028OriginPreservingClassification fixes the origin
(S2888OriginPreserving) and asks for id or alpha.  It is definitionally the
S2888 target (S3028_iff_S2888), and S3028_origin_of_full shows the full
classification would imply it by specialization.

What is still missing:
* a proof of S3028OriginPreservingClassification itself (equivalently
  S2888OriginPreservingOrderTwoClassification);
* the affine/origin classification of the chart-Z coordinate ring, as recorded
  in S2888/S2890/S2978;
* the input that the 2-torsion translation action is nontrivial at the origin
  (equivalently, is excluded by origin preservation).

S2982_rigidity is used only for reflecting identity of strong transformations
from their app component; it does not classify scheme automorphisms and does
not by itself give id-or-alpha.  No classification is faked.
-/

#check S3028OriginPreservingClassification
#check S3028_iff_S2888
#check S3028_id_mem
#check S3028_alpha_mem
#check S3028_full_classification_false_of_translation
#check S3028_origin_of_full
#print axioms S3028_full_classification_false_of_translation
#print axioms S3028_origin_of_full

end LeanFormal.IUT.XiFPaper.S3028OriginPreservingClassification
end
