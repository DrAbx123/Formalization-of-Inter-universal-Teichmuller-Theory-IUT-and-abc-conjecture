import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicUnitPerfection
import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitPerfectionIndTopology

/-!
# The actual arithmetic source with finite-local-field ind topologies

Use the final topology of genuine finite local subfields on the actual
algebraic closure and the final topology of their genuine unit
perfections on the source. Their logarithmic identification is a
homeomorphism, compatible with the original absolute Galois action.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

abbrev sourceAlgebraicFieldIndTopology (place : NumberField.FinitePlace K) :
    TopologicalSpace (SourceAlgebraicClosure place) :=
  algebraicFieldIndTopology (p := (completionRationalPrime place).val)

abbrev sourceUnitPerfectionIndTopology (place : NumberField.FinitePlace K) :
    TopologicalSpace (SourceUnitPerfection place) :=
  algebraicUnitPerfectionIndTopology (p := (completionRationalPrime place).val)

def sourceUnitPerfectionIndHomeomorph (place : NumberField.FinitePlace K) :
    letI := sourceUnitPerfectionIndTopology place
    letI := sourceAlgebraicFieldIndTopology place
    SourceUnitPerfection place ≃ₜ SourceAlgebraicClosure place :=
  algebraicUnitPerfectionIndHomeomorph (p := (completionRationalPrime place).val)

theorem sourceUnitPerfectionIndHomeomorph_mk_one (place : NumberField.FinitePlace K)
    (u : (Integers (SourceAlgebraicClosure place))ˣ) :
    letI := sourceUnitPerfectionIndTopology place
    letI := sourceAlgebraicFieldIndTopology place
    sourceUnitPerfectionIndHomeomorph place (LocalizedModule.mk (Additive.ofMul u) 1) =
      algebraicUnitLog (p := (completionRationalPrime place).val) u :=
  sourceUnitPerfectionEquiv_mk_one place u

theorem sourceUnitPerfectionIndHomeomorph_galois_smul (place : NumberField.FinitePlace K)
    (σ : SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
      SourceAlgebraicClosure place) (x : SourceUnitPerfection place) :
    letI := sourceUnitPerfectionGaloisAction place
    letI := sourceUnitPerfectionIndTopology place
    letI := sourceAlgebraicFieldIndTopology place
    sourceUnitPerfectionIndHomeomorph place (σ • x) =
      σ (sourceUnitPerfectionIndHomeomorph place x) :=
  sourceUnitPerfectionEquiv_galois_smul place σ x

end

end LeanFormal.IUT.NumberFieldFinitePlace
