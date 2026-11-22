import tmp.sheaf.xif.paper.S1519NativeThetaConcreteActual
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # S1543: corrected Gaussian K, exact first missing field data

S1519 proves that the S1280 root with K = F has no SourceClauseC.  A corrected
root must replace only the K level by a finite Galois extension K/F with
K != F that contains the l-torsion kernel field.  This file records that exact
first missing structure; it does not fake a K or a clause C inhabitant. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1543CorrectedGaussianArithmeticActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1519NativeThetaConcreteActual

universe u
variable {l : PrimeGeFive}

/-- The unchanged S1280 Gaussian base arithmetic. -/
abbrev S1543Base (l : PrimeGeFive) := S1280Arithmetic l

/-- Exact first missing corrected K level: finite Galois K/F, nontrivial. -/
structure S1543CorrectedK (l : PrimeGeFive) where
  K : Type u
  [fieldK : Field K]
  [numberFieldK : NumberField K]
  [algebraFK : Algebra (S1543Base l).F K]
  [finiteFK : FiniteDimensional (S1543Base l).F K]
  [galoisFK : IsGalois (S1543Base l).F K]
  /-- K != F, expressed as nontrivial extension degree. -/
  nontrivial : Module.finrank (S1543Base l).F K ≠ 1

attribute [instance] S1543CorrectedK.fieldK S1543CorrectedK.numberFieldK
  S1543CorrectedK.algebraFK S1543CorrectedK.finiteFK S1543CorrectedK.galoisFK

/-- The exact first missing structure for the corrected root: the corrected
K together with the unchanged S1280 Fmod/F/curve data.  No inhabitant is
asserted. -/
structure S1543CorrectedArithmeticRoot (l : PrimeGeFive) where
  correctedK : S1543CorrectedK l
  curve_eq : (S1543Base l).curve =
    (S1280Arithmetic l).curve
  Fmod_eq : (S1280Arithmetic l).Fmod = (S1280Arithmetic l).Fmod
  F_eq : (S1280Arithmetic l).F = (S1280Arithmetic l).F

/-- S1519 is the obstruction for the uncorrected root; restated here for the
consumer boundary. -/
theorem s1543_uncorrected_no_clauseC
    (A : InitialThetaArithmeticData l) (S : SourceSignQuotientData A)
    (C : SourceClauseA A S) (B : SourceClauseB A S C)
    (hKA : Nonempty (A.K ≃ₐ[A.F] A.F))
    (D : SourceClauseC A S C B) : False :=
  S1519_no_sourceClauseC_false (l := l) hKA D

/-- Exact first missing clause-C datum: for a corrected K one must prove
  Nonempty (SourceClauseC A S C B); this file does not assert it. -/
def S1543ClauseCRequired (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : SourceClauseA A S)
    (B : SourceClauseB A S C) : Prop :=
  Nonempty (SourceClauseC A S C B)

end LeanFormal.IUT.XiFPaper.S1543CorrectedGaussianArithmeticActual
end