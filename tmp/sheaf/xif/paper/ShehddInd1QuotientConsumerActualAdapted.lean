import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind1Reduction

/-!
# ShehddInd1QuotientConsumerActualAdapted — Ind1 formal-quotient consumer laws

STEP 0 prior-art (reuse only): IUT III Theorem311/Indeterminacy/Ind1Reduction.lean
proves (namespace LeanFormal.IUT.Theorem311Source): ind1QuotientMap_ind1 (the projection
absorbs the ind1 action), ind1QuotientLift_mk'' (lift commutes with projection),
ind1QuotientLift_unique (uniqueness), and functoriality; the generic quotient transport
lives in Ind1QuotientTransport.lean.

This file exposes the Ind1 quotient laws as consumer statements for the (Ind1) part of
Theorem 3.11.  No new assumptions, no sorry/axiom; the IUT-specific source procession /
Aut-group action carriers remain NAMED (Ind1.lean audit note).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddInd1QuotientConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.MultiradialKernel.Core
open LeanFormal.IUT.Theorem311Source

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- **PROVED consumer:** the Ind1 quotient projection absorbs the `ind1` action. -/
theorem ind1_quotient_absorbs (I : Input Label Choice) (g : Label) (c : Choice) :
    ind1QuotientMap I (I.core.ind1 g c) = ind1QuotientMap I c :=
  ind1QuotientMap_ind1 I g c

/-- **PROVED consumer:** the Ind1 quotient lift commutes with the projection. -/
theorem ind1_lift_mk (I : Input Label Choice) (c : Choice) :
    ind1QuotientLift I (Quotient.mk'' c) = quotientMap I c :=
  ind1QuotientLift_mk'' I c

/-- **PROVED consumer:** the Ind1 quotient lift is the unique map factoring the
projection through the quotient. -/
theorem ind1_lift_unique (I : Input Label Choice)
    (candidate : Quotient (Ind1Setoid I) → IndeterminacyQuotient I)
    (h : ∀ c, candidate (ind1QuotientMap I c) = quotientMap I c) :
    candidate = ind1QuotientLift I :=
  ind1QuotientLift_unique I candidate h

/-- Row record: reused quotient-transport laws vs the consumer interface. -/
def ind1QuotientRows : List (String × String × String) :=
  [ ("projection absorbs ind1 action", "REUSED PROVED", "Ind1Reduction.ind1QuotientMap_ind1")
  , ("lift commutes with projection", "REUSED PROVED", "Ind1Reduction.ind1QuotientLift_mk''")
  , ("lift uniqueness", "REUSED PROVED", "Ind1Reduction.ind1QuotientLift_unique")
  , ("consumer interface", "COMPOSED PROVED", "ind1_quotient_absorbs, ind1_lift_mk, ind1_lift_unique")
  , ("IUT source procession / Aut action / equivariance carriers", "NAMED (audit note)", "Ind1.lean obligation note") ]

theorem ind1QuotientRows_length : ind1QuotientRows.length = 5 := rfl

#check ind1_quotient_absorbs
#check ind1_lift_mk
#check ind1_lift_unique
#check ind1QuotientRows_length

end LeanFormal.IUT.XiFPaper.ShehddInd1QuotientConsumerActualAdapted
end
