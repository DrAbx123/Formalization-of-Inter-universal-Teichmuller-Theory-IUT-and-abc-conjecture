import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual
import Mathlib.Tactic

/-!
# shehdd A661 badPart arithmetic for the inverse bad-prime scaling (Sha)

`badPart e = ∏ b, p_b ^ (e b)` over the bad places: the integer whose prime
support is exactly the inverse-scaled bad primes.  Proved: positivity, nonvanishing,
definitional product form.  This is the arithmetic input of the `badPart` third of
the A661 log/normalized/badPart triple; the log and normalized forms live in
separate files.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleBadPartShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The bad-part integer: product of the bad primes to the inverse-scaling exponents. -/
noncomputable def badPart (e : Bad (nativePlaceSelection T) → Nat) : Nat :=
  ∏ b : Bad (nativePlaceSelection T), qVFamTensorP T b ^ e b

theorem badPart_pos (e : Bad (nativePlaceSelection T) → Nat) :
    0 < badPart T e := by
  unfold badPart
  exact Finset.prod_pos fun b _ =>
    pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime (qVFamTensorP T b))) (e b)

theorem badPart_ne_zero (e : Bad (nativePlaceSelection T) → Nat) :
    badPart T e ≠ 0 :=
  ne_of_gt (badPart_pos T e)

theorem badPart_apply (e : Bad (nativePlaceSelection T) → Nat) :
    badPart T e = ∏ b : Bad (nativePlaceSelection T), qVFamTensorP T b ^ e b :=
  rfl

structure BadPartRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def badPartRows : List BadPartRow :=
  [ ⟨"badPart definition", "product over bad places of p_b^e_b", "GREEN"⟩
  , ⟨"positivity", "badPart_pos", "GREEN"⟩
  , ⟨"nonvanishing", "badPart_ne_zero", "GREEN"⟩
  , ⟨"log/normalized connection", "log of inverse factors = -sum e_b log p_b", "DECISION"⟩
  , ⟨"scope", "arithmetic only; no gap claimed", "INTEGRITY"⟩
  ]

theorem badPartRows_length : badPartRows.length = 5 := rfl

theorem badPartRows_statuses_ok :
    badPartRows.all (fun r =>
      r.status ∈ ["GREEN", "DECISION", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleBadPartShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleBadPartShaActual.badPart_pos
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleBadPartShaActual.badPart_ne_zero
