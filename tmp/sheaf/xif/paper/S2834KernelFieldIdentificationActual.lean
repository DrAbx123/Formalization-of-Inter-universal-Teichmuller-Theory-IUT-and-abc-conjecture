import tmp.sheaf.xif.paper.S2784KernelFieldActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2834KernelFieldIdentificationActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- For the S2784 arithmetic, K is definitionally the 5-torsion kernel field,
so the algebra equivalence is the identity. -/
noncomputable def S2834KernelFieldIdentification :
    arithmetic37.K ≃ₐ[arithmetic37.F]
      (arithmetic37.curve).galoisLTorsionKernelField
        S2771FiveLabel basis37 :=
  AlgEquiv.refl

/-- The identity identification has full range by definition. -/
theorem S2834KernelFieldIdentification_range :
    (Set.range fun x => (S2834KernelFieldIdentification x).1) =
      ((arithmetic37.curve).galoisLTorsionKernelField
        S2771FiveLabel basis37 : Set (AlgebraicClosure arithmetic37.F)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

#check S2834KernelFieldIdentification
#check S2834KernelFieldIdentification_range
#print axioms S2834KernelFieldIdentification
#print axioms S2834KernelFieldIdentification_range

end LeanFormal.IUT.XiFPaper.S2834KernelFieldIdentificationActual
end
