import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilyLawsReduction

/-!
# ShehddHodgeFamilyLawsConsumerActual — Hodge-theater family laws consumer

STEP 0 prior-art (reuse only; A475 search: Hodge theater family laws found):
* IUTI/HodgeTheater/SourceHodgeTheaterFamilyLawsReduction.lean (namespace
  SourceHodgeTheaterFamily): thetaPacket_eq (all theaters share the theta packet),
  theater_eq_of_arithmetic_primeStrip_eq, index_eq_of_arithmetic_primeStrip_eq,
  theater_ne_of_ne, subsingleton_index_of_constant_theater,
  not_constant_theater_of_ne.

This file packages the family laws as one consumer: constancy of the theta packet across
theater indices and distinctness/non-constancy of theater families.  No new assumptions,
no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddHodgeFamilyLawsConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceHodgeTheaterFamily

variable {l : PrimeGeFive} {V : Type*}

/-- **PROVED consumer:** every theater in a Hodge-theater family has the same theta
packet. -/
theorem family_thetaPacket_eq_consumer (F : SourceHodgeTheaterFamily l V)
    (i j : F.index) :
    (F.theater i).thetaPacket = (F.theater j).thetaPacket :=
  SourceHodgeTheaterFamily.thetaPacket_eq F i j

/-- **PROVED consumer:** distinct indices give distinct theaters, and a family is never
constant when its index type is nontrivial. -/
theorem family_distinct_consumer (F : SourceHodgeTheaterFamily l V) {i j : F.index}
    (h : i ≠ j) :
    F.theater i ≠ F.theater j ∧
      ¬ (∀ a b : F.index, F.theater a = F.theater b) :=
  ⟨SourceHodgeTheaterFamily.theater_ne_of_ne F h,
    SourceHodgeTheaterFamily.not_constant_theater_of_ne F h⟩

/-- Row record: reused family laws vs the consumer interface. -/
def hodgeFamilyLawsRows : List (String × String × String) :=
  [ ("theta packet identical across the family", "REUSED PROVED", "SourceHodgeTheaterFamily.thetaPacket_eq")
  , ("arithmetic prime-strip equality determines theater/index", "REUSED PROVED", "theater_eq_of_arithmetic_primeStrip_eq / index_eq_of_arithmetic_primeStrip_eq")
  , ("distinctness and non-constancy", "REUSED PROVED", "theater_ne_of_ne / not_constant_theater_of_ne / subsingleton_index_of_constant_theater")
  , ("consumer bundles", "COMPOSED PROVED", "family_thetaPacket_eq_consumer, family_distinct_consumer")
  , ("concrete family example", "TREE ASSET", "ConcreteHodgeTheaterExample (imported)") ]

theorem hodgeFamilyLawsRows_length : hodgeFamilyLawsRows.length = 5 := rfl

#check family_thetaPacket_eq_consumer
#check family_distinct_consumer
#check hodgeFamilyLawsRows_length

end LeanFormal.IUT.XiFPaper.ShehddHodgeFamilyLawsConsumerActual
end
