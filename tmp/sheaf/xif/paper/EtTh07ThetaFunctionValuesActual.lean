import LeanFormal.IUT.Foundations.Theta.OddTheta

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: oddThetaTerm_zero|oddThetaSign_zero|OddTheta -> hits LeanFormal/IUT/Foundations/Theta/OddTheta.lean:109/113/119/122/139/144 -> REUSE (special values of the EtTh Prop 1.4 theta terms; no re-proof).

# [EtTh] 07: étale theta function object - elementary special values (class A)

Corpus: papers/motizuki_corpus/text/The Etale Theta Function and its Frobenioid-theoretic
Manifestations.txt, Proposition 1.4.  The zero-th and (-1)-st theta terms are the two
terms responsible for the factor 2 in the nonvanishing argument at U = i; the tree
proves their exact values.  This file re-exports them as the class A object-layer
facts of the étale theta function.  No analytic content re-proved; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.EtTh07ThetaFunctionValuesActual

open LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The sign factor at zero is one (reused from OddTheta:109). -/
theorem etTh_oddThetaSign_zero : oddThetaSign (L := L) 0 = 1 :=
  oddThetaSign_zero (L := L)

/-- The sign factor at -1 is minus one (reused from OddTheta:113). -/
theorem etTh_oddThetaSign_neg_one : oddThetaSign (L := L) (-1) = -1 :=
  oddThetaSign_neg_one (L := L)

/-- The zero-th theta term is U (reused from OddTheta:139). -/
theorem etTh_oddThetaTerm_zero (q U : L) : oddThetaTerm q U 0 = U :=
  oddThetaTerm_zero q U

/-- The (-1)-st theta term is -U^(-1) (reused from OddTheta:144). -/
theorem etTh_oddThetaTerm_neg_one (q U : L) : oddThetaTerm q U (-1) = -U⁻¹ :=
  oddThetaTerm_neg_one q U

/-- The zero exponent bookkeeping (reused from OddTheta:119). -/
theorem etTh_oddThetaExponent_zero : oddThetaExponent 0 = 0 :=
  oddThetaExponent_zero

/-- The (-1)-st exponent bookkeeping (reused from OddTheta:122). -/
theorem etTh_oddThetaExponent_neg_one : oddThetaExponent (-1) = 0 :=
  oddThetaExponent_neg_one

#check etTh_oddThetaSign_zero
#check etTh_oddThetaSign_neg_one
#check etTh_oddThetaTerm_zero
#check etTh_oddThetaTerm_neg_one
#check etTh_oddThetaExponent_zero
#check etTh_oddThetaExponent_neg_one

end LeanFormal.IUT.XiFPaper.EtTh07ThetaFunctionValuesActual