import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree
import tmp.sheaf.xif.paper.GenEll01cHeightMulEstimatesActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.XiFPaper.GenEll01bHeightLayerActual

namespace LeanFormal.IUT.XiFPaper.GenEll01dHeightWiringActual

/-- The GenEll height function instantiated at the actual tree height layer (wiring
GenEll §1 abstractions to ArithmeticDivisorDegree hBox). -/
abbrev GenEllPaperHeight {F : Type} [Field F] [NumberField F] : F → Real :=
  fun x => hBox F x

/-- The GenEll height of the identity point is zero (tree wiring): hTerm at 1 is
log(max(1,1)) = 0, hence h_non, h_arc and h vanish. -/
theorem s3135_hTerm_one {F : Type} [Field F] [NumberField F]
    (v : IUTIVPlace F) : hTerm F v (1 : F) = 0 := by
  have h1 : absValAt F v (1 : F) = 1 := by
    cases v with
    | finite v =>
        simpa only [absValAt_finite] using
          (NumberField.HeightOneSpectrum.adicAbv F v).map_one
    | infinite w =>
        simpa only [absValAt_infinite, map_one, one_pow]
  unfold hTerm
  rw [h1]
  norm_num

/-- hBox at the identity point is zero. -/
theorem s3135_hBox_one {F : Type} [Field F] [NumberField F] :
    hBox F (1 : F) = 0 := by
  unfold hBox hNon hArc
  simp only [s3135_hTerm_one]
  simp

/-- GenEll height-layer wiring: mult-subadditivity and nonnegativity, packaged for the
reduction chain (Prop 1.4(i)/(ii) direction actually used). -/
theorem s3135_genEllHeight_mul_le_nonneg {F : Type} [Field F] [NumberField F]
    (x y : F) (hw : 0 ≤ heightWeight F) :
    GenEllPaperHeight (F := F) (x * y) ≤
        GenEllPaperHeight (F := F) x + GenEllPaperHeight (F := F) y ∧
      0 ≤ GenEllPaperHeight (F := F) x :=
  ⟨hBox_mul_le F x y, s3135_hBox_nonneg x hw⟩

def s3135HeightWiringCitations : List (String × String) :=
  [ ("hBox/hTerm wiring", "ArithmeticDivisorDegree.lean:1171 hTerm, :1220-1228 hNon/hArc/hBox; absValAt_one"),
    ("GenEll use", "Prop 1.4(i) product direction (subadditivity, Lemma 1.3(iv) :1407) + Prop 1.4(ii) lower bound; packaged for mainline reduction inputs") ]

theorem s3135HeightWiringCitations_length : s3135HeightWiringCitations.length = 2 := rfl

#check GenEllPaperHeight
#check s3135_hTerm_one
#check s3135_hBox_one
#check s3135_genEllHeight_mul_le_nonneg
end LeanFormal.IUT.XiFPaper.GenEll01dHeightWiringActual
end