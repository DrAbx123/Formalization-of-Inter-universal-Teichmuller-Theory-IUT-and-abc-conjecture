import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import tmp.sheaf.xif.paper.S1298TorsionClauseActual
import tmp.sheaf.xif.paper.S1543CorrectedGaussianArithmeticActual

/-! # S1544: l-torsion representation and kernel field for the Gaussian curve

For the actual Gaussian punctured elliptic curve, construct the Galois
representation on E[l] and the fixed kernel field, with the actual
finite/Galois instances.  The rank-two basis is the first missing input; the
large-image SL2 statement and kernel-field identification are exact fields. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1544LTorsionKernelFieldActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

variable {l : PrimeGeFive}

/-- The actual Gaussian punctured elliptic curve. -/
abbrev GaussianCurve : PuncturedEllipticCurve (S1280Arithmetic l).F :=
  (S1280Arithmetic l).curve

/-- Exact first missing input: a rank-two `ZMod l`-basis of E[l]. -/
abbrev GaussianTorsionBasis (l : PrimeGeFive) : Type :=
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
    (GaussianCurve (l := l)).LTorsion l

/-- The actual l-torsion Galois representation, given a rank-two basis. -/
noncomputable def gaussianLTorsionRepresentation
    (b : GaussianTorsionBasis l) :
    (AlgebraicClosure (S1280Arithmetic l).F ≃ₐ[(S1280Arithmetic l).F]
      AlgebraicClosure (S1280Arithmetic l).F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  (GaussianCurve (l := l)).galoisLTorsionMatrixRepresentation l b

/-- The actual kernel field L = fixed field of the representation kernel. -/
noncomputable def gaussianKernelField
    (b : GaussianTorsionBasis l) :
    IntermediateField (S1280Arithmetic l).F
      (AlgebraicClosure (S1280Arithmetic l).F) :=
  (GaussianCurve (l := l)).galoisLTorsionKernelField l b

/-- Exact kernel-field identification property for the source field K. -/
def GaussianKernelFieldIdentification
    (b : GaussianTorsionBasis l) : Prop :=
  Nonempty ((S1280Arithmetic l).K ≃ₐ[(S1280Arithmetic l).F]
    (gaussianKernelField (l := l) b))

/-- Exact large-image input: the actual S1298 large-image field, whose first
component is a rank-two basis. -/
abbrev GaussianLargeImageFirstField (l : PrimeGeFive) : Prop :=
  LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual.S1298LargeImageField l

/-- L/F is finite, from the actual Krull-open kernel. -/
instance gaussianKernelField_finiteDimensional
    (b : GaussianTorsionBasis l) :
    FiniteDimensional (S1280Arithmetic l).F
      (gaussianKernelField (l := l) b) :=
  (GaussianCurve (l := l)).galoisLTorsionKernelField_finiteDimensional l b

/-- L/F is Galois, from normality of the representation kernel. -/
instance gaussianKernelField_isGalois
    (b : GaussianTorsionBasis l) :
    IsGalois (S1280Arithmetic l).F (gaussianKernelField (l := l) b) :=
  (GaussianCurve (l := l)).galoisLTorsionKernelField_isGalois l b

/-- The fixing subgroup of L is exactly the representation kernel. -/
theorem gaussianKernelField_fixingSubgroup
    (b : GaussianTorsionBasis l) :
    (gaussianKernelField (l := l) b).fixingSubgroup =
      (gaussianLTorsionRepresentation (l := l) b).ker := by
  exact (GaussianCurve (l := l)).galoisLTorsionKernelField_fixingSubgroup l b

/-- The kernel field is a number field over the number-field base. -/
instance gaussianKernelField_numberField
    (b : GaussianTorsionBasis l) :
    NumberField (gaussianKernelField (l := l) b) :=
  (GaussianCurve (l := l)).galoisLTorsionKernelField_numberField l b

/-- Conditional bridge: a rank-two basis plus the nontrivial-degree proof yields
the S1543 corrected K with K = the actual l-torsion kernel field. -/
noncomputable def s1543CorrectedKOfBasis
    (b : GaussianTorsionBasis l)
    (hnt : Module.finrank (S1280Arithmetic l).F
      (gaussianKernelField (l := l) b) ≠ 1) :
    LeanFormal.IUT.XiFPaper.S1543CorrectedGaussianArithmeticActual.S1543CorrectedK l where
  K := gaussianKernelField (l := l) b
  nontrivial := hnt

end LeanFormal.IUT.XiFPaper.S1544LTorsionKernelFieldActual

end
