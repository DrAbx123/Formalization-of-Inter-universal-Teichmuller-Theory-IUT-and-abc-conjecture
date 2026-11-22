import tmp.sheaf.n8.closure.PaperOrbicurveClauseActual

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Unconditional paper orbicurve clause with identity cover

The five geometric donors are instantiated by actual data:
puncturedCurve = cover = PuncturedEllipticCurve F, and the two maps are
identity.  The resulting SourceOrbicurveClause is unconditional.  This only
constructs the identity-cover special case; a nontrivial etale cover is not
constructed, which is the exact geometric-semantics gap.  No arbitrary
PUnit/True is used.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.N8Closure.PaperOrbicurveClauseConstructed

variable {l : PrimeGeFive}

variable (S : SourceInitialThetaData.{0} l)
variable (C : ClauseD l S.candidate)

/-- Actual identity-cover donors. -/
noncomputable def identityOrbicurveDonors :
    PaperOrbicurveClauseActual.PaperOrbicurveDonors S where
  puncturedCurve := PuncturedEllipticCurve S.candidate.arithmetic.F
  cover := PuncturedEllipticCurve S.candidate.arithmetic.F
  curveToPunctured := id
  coverToPunctured := id
  cover_surjective := Function.surjective_id

/-- Unconditional actual SourceOrbicurveClause from the paper candidate. -/
noncomputable def paperOrbicurveClause :
    SourceOrbicurveClause.{0, 0, 0} :=
  PaperOrbicurveClauseActual.paperOrbicurveClause S C
    (identityOrbicurveDonors S)

theorem paperOrbicurveClause_curve :
    (paperOrbicurveClause S C).curve =
      PuncturedEllipticCurve S.candidate.arithmetic.F := rfl

theorem paperOrbicurveClause_exactSequence :
    (paperOrbicurveClause S C).exactSequence =
      PaperOrbicurveClauseActual.paperExactSequence C.xK_exact_sequence := rfl

theorem paperOrbicurveClause_cuspCount :
    (paperOrbicurveClause S C).cuspCount =
      S.candidate.xF.signature.punctures := rfl

theorem paperOrbicurveClause_cover_surjective :
    Function.Surjective (paperOrbicurveClause S C).coverToPunctured :=
  (paperOrbicurveClause S C).cover_surjective

/-- Exact semantic gap: the cover is the identity, so no nontrivial etale
cover of the punctured curve is constructed. -/
def NontrivialCoverSemanticGap : Prop :=
  (paperOrbicurveClause S C).coverToPunctured = id ∧
    (paperOrbicurveClause S C).puncturedCurve =
      PuncturedEllipticCurve S.candidate.arithmetic.F

theorem nontrivialCoverSemanticGap : NontrivialCoverSemanticGap S C :=
  ⟨rfl, rfl⟩

end LeanFormal.IUT.N8Closure.PaperOrbicurveClauseConstructed

end
