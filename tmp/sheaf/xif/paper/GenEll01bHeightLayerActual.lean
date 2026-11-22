import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree
import tmp.sheaf.xif.paper.GenEll01BasicActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.XiFPaper.GenEll01BasicActual

namespace LeanFormal.IUT.XiFPaper.GenEll01bHeightLayerActual

/-- The paper height layer of GenEll §1 is the tree's arithmetic-divisor-degree height
layer h = h_non + h_arc (ArithmeticDivisorDegree.lean:1171 hTerm, :1214 heightWeight,
:1220-1236 hNon/hArc/hBox; EE L452-475). -/
abbrev paperHeightFn (F : Type) [Field F] [NumberField F] (x : F) : Real :=
  hBox F x

/-- GenEll Prop 1.4(ii)-support (heights bounded below) instantiated at the tree height
layer: h_non >= 0 pointwise, given the weight is nonnegative. -/
theorem s3135_hNon_nonneg {F : Type} [Field F] [NumberField F] (x : F)
    (hw : 0 ≤ heightWeight F) : 0 ≤ hNon F x := by
  unfold hNon
  exact mul_nonneg hw (Finset.sum_nonneg (fun v _ => hTerm_nonneg F (.finite v) x))

/-- h_arc >= 0 pointwise (tree hTerm_nonneg). -/
theorem s3135_hArc_nonneg {F : Type} [Field F] [NumberField F] (x : F)
    (hw : 0 ≤ heightWeight F) : 0 ≤ hArc F x := by
  unfold hArc
  exact mul_nonneg hw (Finset.sum_nonneg (fun w _ => hTerm_nonneg F (.infinite w) x))

/-- h = h_non + h_arc >= 0 pointwise (GenEll Prop 1.4(ii) lower-bound direction at the
tree height layer). -/
theorem s3135_hBox_nonneg {F : Type} [Field F] [NumberField F] (x : F)
    (hw : 0 ≤ heightWeight F) : 0 ≤ hBox F x :=
  add_nonneg (s3135_hNon_nonneg x hw) (s3135_hArc_nonneg x hw)

/-- Tree-exported height-layer facts re-stated for GenEll consumption. -/
theorem s3135_hTerm_nonneg_reuse {F : Type} [Field F] [NumberField F]
    (v : IUTIVPlace F) (x : F) : 0 ≤ hTerm F v x :=
  hTerm_nonneg F v x

def s3135HeightLayerCitations : List (String × String) :=
  [ ("hTerm/hTerm_nonneg", "ArithmeticDivisorDegree.lean:1171/1177 (EE L452-458)"),
    ("heightWeight", "ArithmeticDivisorDegree.lean:1214 (1/[F:Q])"),
    ("hNon/hArc/hBox", "ArithmeticDivisorDegree.lean:1220/1224/1228 (EE L452-459)"),
    ("GenEll Prop 1.4(ii)", "corpus 311-316: ht_L bounded below on nonzero-section locus; at the tree layer h_non,h_arc,h >= 0") ]

theorem s3135HeightLayerCitations_length : s3135HeightLayerCitations.length = 4 := rfl

#check paperHeightFn
#check s3135_hBox_nonneg
#check s3135_hTerm_nonneg_reuse
end LeanFormal.IUT.XiFPaper.GenEll01bHeightLayerActual
end
