import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree
import tmp.sheaf.xif.paper.GenEll01bHeightLayerActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.XiFPaper.GenEll01bHeightLayerActual

namespace LeanFormal.IUT.XiFPaper.GenEll01cHeightMulEstimatesActual

/-- **GenEll height product estimate (tree Lemma 1.3(iv), reused)**: the actual tree
height h = h_non + h_arc is subadditive under multiplication, which is the direction of
the paper's height comparisons needed in the (ii)=>(i) reduction chain
(ArithmeticDivisorDegree.lean:1407 hBox_mul_le; :1369 hNon_mul_le; :1392 hArc_mul_le). -/
theorem s3135_hBox_mul_le_reuse {F : Type} [Field F] [NumberField F] (x y : F) :
    hBox F (x * y) ≤ hBox F x + hBox F y :=
  hBox_mul_le F x y

/-- The same subadditivity for the paper-height abbreviation of GenEll01b. -/
theorem s3135_paperHeight_mul_le {F : Type} [Field F] [NumberField F] (x y : F) :
    paperHeightFn F (x * y) ≤ paperHeightFn F x + paperHeightFn F y :=
  hBox_mul_le F x y

/-- Non-archimedean part subadditivity (reused). -/
theorem s3135_hNon_mul_le_reuse {F : Type} [Field F] [NumberField F] (x y : F) :
    hNon F (x * y) ≤ hNon F x + hNon F y :=
  hNon_mul_le F x y

/-- Archimedean part subadditivity (reused). -/
theorem s3135_hArc_mul_le_reuse {F : Type} [Field F] [NumberField F] (x y : F) :
    hArc F (x * y) ≤ hArc F x + hArc F y :=
  hArc_mul_le F x y

def s3135HeightMulCitations : List (String × String) :=
  [ ("tree Lemma 1.3(iv)", "ArithmeticDivisorDegree.lean:1369 hNon_mul_le / :1392 hArc_mul_le / :1407 hBox_mul_le (subadditivity under product; EE L452-475)"),
    ("GenEll usage", "Prop 1.4(i)/(iii) comparisons and the (ii)=>(i) reduction use the height product/subadditivity direction; tree supplies it as reusable proved lemma") ]

theorem s3135HeightMulCitations_length : s3135HeightMulCitations.length = 2 := rfl

#check s3135_paperHeight_mul_le
#check s3135_hBox_mul_le_reuse
end LeanFormal.IUT.XiFPaper.GenEll01cHeightMulEstimatesActual
end
