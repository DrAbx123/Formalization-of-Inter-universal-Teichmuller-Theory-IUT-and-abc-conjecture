import tmp.sheaf.xif.paper.Mzk1Cor312AcceptedFinalActual
import tmp.sheaf.xif.paper.Mzk1Cor312SignedMagnitudeChecksActual
import tmp.sheaf.xif.paper.Mzk1Cor312RequirementSignedChecksActual

/-!
# A574 ABC Stage-5 evidence pack (shehdd resolved-acceptance side)

Prints axiom dependencies of the resolved-acceptance facts contributed by
shehdd's lane: signed paper inequality, strict reading, `C_Theta` form,
requirement-level signed inequalities, and the signed/magnitude equivalence.

These are the facts ABC Stage-5 / height-bound consumers may cite; expected
axioms only `[propext, Classical.choice, Quot.sound]`.

No sorry/axiom/True declarations are added here.
-/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual.accepted_signed_inequality
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual.accepted_strict
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual.accepted_CTheta
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual.accepted_magnitude_iff
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedMagnitudeChecksActual.signed_ineq_iff_magnitude
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementSignedChecksActual.requirement_CTheta_ge_neg_one
