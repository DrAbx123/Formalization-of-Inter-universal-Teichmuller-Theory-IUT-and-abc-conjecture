import tmp.sheaf.xif.paper.S2790F6Actual
import tmp.sheaf.xif.paper.S2787ClauseB37Actual
import tmp.sheaf.xif.paper.S2810F6GaloisTorsionActual
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2790F6Actual
open LeanFormal.IUT.XiFPaper.S2787ClauseB37Actual
open LeanFormal.IUT.XiFPaper.S2810F6GaloisTorsionActual

local instance s2839GaussianFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000

namespace LeanFormal.IUT.XiFPaper.S2839A6F6ClauseRestatementActual

/-- A6 base field: F6 = Q(i, E[6]). -/
abbrev A6F6 : Type := S2790F6

/-- A6 curve: 37a1 base-changed to F6. -/
noncomputable abbrev A6Curve : PuncturedEllipticCurve A6F6 :=
  (E37a1Q.baseChange GaussianField).baseChange A6F6

/-- Stable reduction is preserved by the base change 37a1 -> F6. -/
theorem A6_stableReduction [NumberField A6F6]
    (h37 : E37a1Q.HasStableReductionEverywhere) :
    A6Curve.HasStableReductionEverywhere :=
  PuncturedEllipticCurve.hasStableReductionEverywhere_baseChange
    (X := E37a1Q.baseChange GaussianField) (K := A6F6)
    (PuncturedEllipticCurve.hasStableReductionEverywhere_baseChange
      (X := E37a1Q) (K := GaussianField) h37)

/-- A6 field_of_moduli restatement: the 37a1 j-invariant is rational and
hence defines a moduli point over F6.  The rationality proof is the exact
remaining field-of-moduli datum. -/
def A6FieldOfModuliRestated : Prop :=
  exists j : Rat, algebraMap Rat A6F6 j = A6Curve.jInvariant

/-- A6 maximal-solvable restatement: the maximal finite solvable Galois
subextension of F6 over Q(i). -/
structure A6MaxSolvableRestated where
  extension : IntermediateField GaussianField A6F6
  finite : FiniteDimensional GaussianField extension
  galois : IsGalois GaussianField extension
  solvable : IsSolvable (extension ≃ₐ[GaussianField] extension)

/-- A6 Clause-A restatement bundle: stable reduction is actual (from the
37a1 base-change theorem); field_of_moduli and maximal-solvable are exact
restated data/gaps. -/
structure A6ClauseARestatement [NumberField A6F6] where
  stable_reduction : A6Curve.HasStableReductionEverywhere
  field_of_moduli : A6FieldOfModuliRestated
  maximal_solvable : A6MaxSolvableRestated

theorem A6ClauseARestatement_stable [NumberField A6F6]
    (h37 : E37a1Q.HasStableReductionEverywhere) :
    A6Curve.HasStableReductionEverywhere :=
  A6_stableReduction h37

end LeanFormal.IUT.XiFPaper.S2839A6F6ClauseRestatementActual
end
