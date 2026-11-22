import tmp.sheaf.xif.paper.NativeBadSetFiniteActual
import tmp.sheaf.xif.paper.NativeSourceAssemblyFieldsActual
import tmp.sheaf.xif.paper.NativeSourceAssemblyActual
import tmp.sheaf.n8.closure.NativeSourceTorsionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.n8.closure.NativeBadLiftActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual NativeSourceAssembly fields: badFinite, carriers, torsion objects

This file fills the actual fields available from the native clauses:
* badFinite: actual nativeBadSetFiniteField;
* curve/puncturedCurve/cover/structureGroup and point maps: actual
  actualNativeAssemblyCarrierFields;
* torsion carrier and rank-two basis: actual clause-C data.

The remaining fields split / torsionGaps / exactSequence (splitting section)
/ cuspCount / d7 / cuspHyp / compatibility proofs have no unconditional actual
constructor in the current tree. They are not replaced by True/PUnit or
arbitrary data.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeSourceAssemblyActualFields

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.NativeBadSetFiniteActual
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyFieldsActual

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual part of NativeSourceAssemblyFields constructed from clause A-D data. -/
structure ActualExactSequencePart where
  inclusionInjective :
    Function.Injective X.S.clauseD.x_groups.sequence.inclusion
  projectionSurjective :
    Function.Surjective X.S.clauseD.x_groups.sequence.projection
  exactness :
    X.S.clauseD.x_groups.sequence.inclusion.hom.range =
      X.S.clauseD.x_groups.sequence.projection.hom.ker

/-- The actual clause-D exact sequence data. -/
noncomputable def actualExactSequencePart :
    ActualExactSequencePart X where
  inclusionInjective := X.S.clauseD.x_groups.sequence.inclusion_injective
  projectionSurjective := X.S.clauseD.x_groups.sequence.projection_surjective
  exactness := X.S.clauseD.x_groups.sequence.exact

structure NativeSourceAssemblyActualPart where
  badFinite : NativeBadSetFinite X.S
  torsionCarrier : Type u
  torsionBasis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      X.S.arithmetic.curve.LTorsion l
  torsion23Rational :
    PuncturedEllipticCurve.Torsion23Rational X.S.arithmetic.curve
  galoisRepresentation :
    SourceAbsoluteGalois X.S.arithmetic →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)
  geometricCusp :
    Iut.OrbicurveBoundaryCusp X.S.tuple.cK
  exactSequence : ActualExactSequencePart X
  redCompat : Prop
  redCompat_proved : redCompat
  torCompat : Prop
  torCompat_proved : torCompat
  orbCompat : Prop
  orbCompat_proved : orbCompat
  secCompat : Prop
  secCompat_proved : secCompat
  cusCompat : Prop
  cusCompat_proved : cusCompat

/-- The actual fields: finite bad set, orbicurve carriers, torsion carrier. -/
noncomputable def nativeSourceAssemblyActualPart :
    NativeSourceAssemblyActualPart X where
  badFinite := nativeBadSetFiniteField (X := X)
  torsionCarrier := Multiplicative (X.S.arithmetic.curve.LTorsion l)
  torsionBasis := X.S.clauseC.torsion_basis
  torsion23Rational := X.S.clauseC.torsion23_rational
  galoisRepresentation := X.S.clauseC.representation
  geometricCusp := X.S.tuple.epsilon
  exactSequence := actualExactSequencePart X
  redCompat :=
    ∀ b : Bad (nativePlaceSelection X.S),
      X.S.arithmetic.curve.HasMultiplicativeReductionAt
        ((nativeBadLift X.S).lift b)
  redCompat_proved := by
    intro b
    exact X.S.clauseB.multiplicative_over_bad ((nativeBadLift X.S).lift b)
      (by rw [(nativeBadLift X.S).lift_comap]; exact b.2)
  torCompat :=
    Nonempty ((Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      X.S.arithmetic.curve.LTorsion l)
  torCompat_proved := ⟨X.S.clauseC.torsion_basis⟩
  orbCompat :=
    Nonempty (SourceOrbicurveFiniteEtaleCover
      X.S.tuple.source.xK X.S.tuple.source.cK)
  orbCompat_proved := ⟨X.S.clauseD.k_l_torsion_cover⟩
  secCompat :=
    Nonempty (∀ (v : {v : NumberFieldPlace X.S.arithmetic.K //
        v ∈ X.S.tuple.source.V}) (hv : v.1.IsFinite),
      SourceFiniteLocalSource X.S.arithmetic X.S.tuple.source X.S.clauseA
        X.S.clauseB X.S.clauseC X.S.clauseD (selectedFinitePlace hv))
  secCompat_proved := ⟨X.S.clauseE.finite_local⟩
  cusCompat :=
    X.S.clauseF.boundary_origin.cusp = X.S.tuple.source.epsilon
  cusCompat_proved := X.S.clauseF.boundary_cusp_eq_epsilon

/-- The actual torsion basis is the clause-C rank-two basis. -/
theorem nativeSourceAssemblyActualPart_torsionBasis :
    (nativeSourceAssemblyActualPart (l := l) X).torsionBasis =
      X.S.clauseC.torsion_basis := rfl

end LeanFormal.IUT.XiFPaper.NativeSourceAssemblyActualFields

end
