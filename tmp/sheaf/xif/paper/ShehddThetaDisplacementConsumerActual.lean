import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkDisplacementReduction

/-!
# ShehddThetaDisplacementConsumerActual — theta-link displacement consumer

STEP 0 prior-art (reuse only; A475 search: HodgeTheater displacement found):
* IUTI/HodgeTheater/SourceThetaLinkDisplacementReduction.lean:
  ThetaQDisplacement, ThetaScaleDisplacement,
  hodgeTheaterLink_displacement, hodgeTheaterLink_scaleDisplacement,
  thetaQDisplacement_refl/symm/trans.

This file packages the theta-link displacement laws as one consumer: a Hodge theater link
displaces q and every scale, and q-displacement is an equivalence relation.  No new
assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddThetaDisplacementConsumerActual

open LeanFormal.IUT

universe ua uv upi umon

variable {l : PrimeGeFive} {V : Type uv}

/-- **PROVED consumer:** a Hodge theater link displaces the q-packet and all scales. -/
theorem thetaDisplacement_link_consumer
    {A B : HodgeTheater.{ua, uv, upi, umon} l V} (L : HodgeTheaterLink A B) :
    ThetaQDisplacement A B ∧ (∀ j : SignedLabel l.value, ThetaScaleDisplacement A B j) :=
  ⟨hodgeTheaterLink_displacement L,
    fun j => hodgeTheaterLink_scaleDisplacement L j⟩

/-- **PROVED consumer:** q-displacement is reflexive/symmetric/transitive. -/
theorem thetaDisplacement_equivalence_consumer
    (A B C : HodgeTheater.{ua, uv, upi, umon} l V) :
    ThetaQDisplacement A A ∧
      (ThetaQDisplacement A B → ThetaQDisplacement B A) ∧
        (ThetaQDisplacement A B → ThetaQDisplacement B C → ThetaQDisplacement A C) :=
  ⟨thetaQDisplacement_refl A,
    fun h => thetaQDisplacement_symm h,
    fun h1 h2 => thetaQDisplacement_trans h1 h2⟩

/-- Row record: reused displacement laws vs the consumer interface. -/
def thetaDisplacementRows : List (String × String × String) :=
  [ ("q/scale displacement definitions", "REUSED DEF", "ThetaQDisplacement / ThetaScaleDisplacement")
  , ("link implies displacement", "REUSED PROVED", "hodgeTheaterLink_displacement / _scaleDisplacement")
  , ("q-displacement equivalence laws", "REUSED PROVED", "thetaQDisplacement_refl/symm/trans")
  , ("consumer bundles", "COMPOSED PROVED", "thetaDisplacement_link_consumer, thetaDisplacement_equivalence_consumer")
  , ("full source theta-link data (packet families / LGP action)", "TREE LAYER (see HodgeTheater module)", "carried by HodgeTheaterFamilyLawsReduction imports") ]

theorem thetaDisplacementRows_length : thetaDisplacementRows.length = 5 := rfl

#check thetaDisplacement_link_consumer
#check thetaDisplacement_equivalence_consumer
#check thetaDisplacementRows_length

end LeanFormal.IUT.XiFPaper.ShehddThetaDisplacementConsumerActual
end
