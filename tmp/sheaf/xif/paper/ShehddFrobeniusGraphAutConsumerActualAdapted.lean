import tmp.sheaf.xif.paper.Mzk1FrobeniusGraphAutClosureActual

/-!
# ShehddFrobeniusGraphAutConsumerActualAdapted — Frobenius-picture graph automorphism consumer

STEP 0 prior-art (reuse only; A475 search hits):
* IUTI/HodgeTheater/SourceThetaLinkGraphAutomorphismReduction.lean:
  FrobeniusPictureGraphAut, chainTranslation, chainTranslation_graphAut, graphAut_one,
  graphAut_translation, graphAut_eq_translation (Aut(Gamma) = translations),
  graphAut_comp, graphAut_symm;
* Mzk1FrobeniusGraphAutClosureActual: FrobeniusPictureGraphAut_inv / _mul / _pow.

This file exposes the graph-automorphism group closure together with the translation
classification as one consumer statement.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddFrobeniusGraphAutConsumerActualAdapted

open LeanFormal.IUT

/-- **PROVED consumer:** graph automorphisms of the Frobenius picture are exactly the
translations, and they form a group closed under inverse, multiplication and powers. -/
theorem frobenius_graphAut_closure_summary (σ τ : Equiv.Perm Int) :
    (FrobeniusPictureGraphAut σ ↔ ∃ k : Int, σ = chainTranslation k) ∧
      (FrobeniusPictureGraphAut σ → FrobeniusPictureGraphAut σ⁻¹) ∧
      (FrobeniusPictureGraphAut σ → FrobeniusPictureGraphAut τ →
        FrobeniusPictureGraphAut (σ * τ)) ∧
      (∀ k : Int, FrobeniusPictureGraphAut (chainTranslation k)) :=
  ⟨graphAut_eq_translation σ,
    fun h => FrobeniusPictureGraphAut_inv h,
    fun h1 h2 => FrobeniusPictureGraphAut_mul h1 h2,
    fun k => chainTranslation_graphAut k⟩

/-- **PROVED consumer:** the translation parameter of a graph automorphism (its
additive shift), and injectivity of the parameter. -/
theorem frobenius_graphAut_translation_parameter (σ : Equiv.Perm Int)
    (hσ : FrobeniusPictureGraphAut σ) :
    ∃ k : Int, ∀ n : Int, σ n = n + k :=
  graphAut_translation σ hσ

/-- **PROVED consumer:** the translation parameter is injective. -/
theorem frobenius_chainTranslation_injective :
    Function.Injective chainTranslation :=
  chainTranslation_injective

/-- Row record: reused graph-aut laws vs consumer statements. -/
def frobeniusGraphAutRows : List (String × String × String) :=
  [ ("Aut(Gamma) = translations", "REUSED PROVED", "SourceThetaLinkGraphAutomorphismReduction.graphAut_eq_translation")
  , ("translation is a graph automorphism; parameter injective", "REUSED PROVED", "chainTranslation_graphAut / chainTranslation_injective")
  , ("group closure inv/mul/pow", "REUSED PROVED", "Mzk1FrobeniusGraphAutClosureActual.FrobeniusPictureGraphAut_inv/_mul/_pow")
  , ("consumer closure summary", "COMPOSED PROVED", "frobenius_graphAut_closure_summary")
  , ("additive parameter extraction", "REUSED PROVED", "graphAut_translation") ]

theorem frobeniusGraphAutRows_length : frobeniusGraphAutRows.length = 5 := rfl

#check frobenius_graphAut_closure_summary
#check frobenius_graphAut_translation_parameter
#check frobenius_chainTranslation_injective
#check frobeniusGraphAutRows_length

end LeanFormal.IUT.XiFPaper.ShehddFrobeniusGraphAutConsumerActualAdapted
end
