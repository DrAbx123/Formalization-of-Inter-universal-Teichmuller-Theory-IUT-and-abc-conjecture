import Mathlib.FieldTheory.Separable

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2533NonmonicCardRootSetActual

/-- Non-monic version of the root-set cardinality formula: separability plus
splitting over the target field suffice; monicity is not needed. -/
theorem S2533_nonmonic_card_rootSet
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {f : F[X]} (hsep : f.Separable) (hsplit : f.Splits) :
    Fintype.card (f.rootSet K) = f.natDegree :=
  Polynomial.card_rootSet_eq_natDegree hsep hsplit

#print axioms S2533_nonmonic_card_rootSet
end LeanFormal.IUT.XiFPaper.S2533NonmonicCardRootSetActual
end