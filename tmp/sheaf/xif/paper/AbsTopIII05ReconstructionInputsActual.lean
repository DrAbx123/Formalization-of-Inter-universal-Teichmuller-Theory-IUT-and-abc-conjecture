set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: MonoAnalyticLogShellArchPsiCnsCalibration|Prop 5.8|Cor 5.5|SourceThetaLinkGraphAutomorphismReduction -> hits IUTII/Kummer/MonoAnalyticLogShellArchPsiCnsCalibration.lean, IUTI/HodgeTheater/SourceThetaLinkGraphAutomorphismReduction.lean:11 -> DEEP inputs NOT proved; only precise naming.

# [AbsTopIII] 05: precisely named DEEP inputs (NO proof claimed)

Corpus: papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt.
These are the anabelian/deep inputs that our concrete p-adic route does NOT need:

(D1) Prop 5.8 (i) (corpus 8059-8075): group-theoretic reconstruction of the images
     of O^diamond_k -> G_ab, k^x -> G_ab of local class field theory, including p,
     p*, residue cardinality p^f, absolute degree, ramification index, order p^m of
     p-th power roots of unity.
(D2) Prop 5.8 (ii) (corpus 8076-8096): functorial group-theoretic algorithm
     Ob(TG^vdash) ∋ G |-> Gamma^x_non(G) constructing the Gamma^x_non-diagram and
     the log-shell I(G) inside k^~(G).
(D3) Cor 5.5 (corpus 7347-7390): global and panalocal mono-anabelian log-Frobenius
     compatibility (diagram D^bullet and functorial compatibilities).
(D4) Section 0 oriented graph Gamma (corpus 1269): the oriented graph / combinatorial
     anabelian data; tree has only the automorphism-reduction interface.

Status: NONE of D1-D4 is proved or imported as a theorem; recorded as deep
anabelian inputs with corpus citations.  Our concrete-data route does not invoke them.
-/

namespace LeanFormal.IUT.XiFPaper.AbsTopIII05ReconstructionInputsActual

/-- Classification tag for deep inputs. -/
inductive DeepInputKind where
  | prop58i
  | prop58ii
  | cor55
  | orientedGraph
  deriving DecidableEq, Repr

/-- A precisely named deep input (corpus citation only; NO proof claimed). -/
structure DeepInput where
  kind : DeepInputKind
  statement : String
  corpus : String
  treeAnchor : String
  proved : Bool

/-- The four deep inputs of [AbsTopIII] that our concrete route does not need. -/
def absTopIIIDeepInputs : List DeepInput :=
  [ { kind := .prop58i, statement := "group-theoretic reconstruction of O^diamond_k and k^x embeddings (p, p*, p^f, [k:Qp], e, p^m)",
      corpus := "AbsTopIII corpus 8059-8075 (Prop 5.8(i))",
      treeAnchor := "none (deep anabelian input)", proved := false }
  , { kind := .prop58ii, statement := "functorial Gamma^x_non diagram + log-shell I(G) reconstruction",
      corpus := "AbsTopIII corpus 8076-8096 (Prop 5.8(ii))",
      treeAnchor := "none (deep anabelian input)", proved := false }
  , { kind := .cor55, statement := "global/panalocal mono-anabelian log-Frobenius compatibility",
      corpus := "AbsTopIII corpus 7347-7390 (Cor 5.5)",
      treeAnchor := "SourceLogShellAbsTopIIIBridge:6/10/15 (dictionary only)", proved := false }
  , { kind := .orientedGraph, statement := "oriented graph Gamma^x_v (combinatorial anabelian data)",
      corpus := "AbsTopIII corpus 1269 (Section 0)",
      treeAnchor := "SourceThetaLinkGraphAutomorphismReduction:11 (automorphism interface only)", proved := false } ]

/-- There are exactly four deep inputs. -/
theorem absTopIIIDeepInputs_length : absTopIIIDeepInputs.length = 4 := rfl

/-- None of the deep inputs is claimed as proved. -/
theorem absTopIIIDeepInputs_none_proved :
    absTopIIIDeepInputs.all (fun d => !d.proved) = true := rfl

#check DeepInputKind
#check DeepInput
#check absTopIIIDeepInputs
#check absTopIIIDeepInputs_length
#check absTopIIIDeepInputs_none_proved

end LeanFormal.IUT.XiFPaper.AbsTopIII05ReconstructionInputsActual