import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiPunctureInfinityCriterion

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-!
# Source-Psi evaluation dichotomy

Combines the actual puncture trichotomy with the coordinate-ring evaluation and
unit-map surjectivity.  The three cases are: point at infinity, affine with
nonintegral coordinates, and affine integral with an actual evaluation datum.
No point or evaluation is fabricated.
-/

namespace LeanFormal.IUT.SourcePsiEvaluationDichotomy

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiPunctureInfinityCriterion
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev PunctureCurve : WeierstrassCurve (v.adicCompletion S.arithmetic.F) :=
  (SourcePunctureBaseChange S v).curve

abbrev PunctureCoordinateRing : Type u :=
  WeierstrassCurve.Affine.CoordinateRing (PunctureCurve S v)

/-- Evaluation at actual affine coordinates. -/
noncomputable def punctureEvaluationOfCoordinates
    (C : SourcePsiPunctureAffineCoordinates S v) :
    PunctureCoordinateRing S v →+* v.adicCompletion S.arithmetic.F :=
  AdjoinRoot.lift (Polynomial.evalRingHom C.x) C.y
    (by simpa [PunctureCoordinateRing, PunctureCurve] using C.nonsingular.1)

theorem punctureEvaluationOfCoordinates_algebraMap
    (C : SourcePsiPunctureAffineCoordinates S v) :
    (punctureEvaluationOfCoordinates S v C).comp
        (algebraMap (v.adicCompletion S.arithmetic.F)
          (PunctureCoordinateRing S v)) =
      RingHom.id (v.adicCompletion S.arithmetic.F) := by
  ext r
  simp [punctureEvaluationOfCoordinates, AdjoinRoot.lift_of]

/-- Actual evaluation/retraction datum for the puncture coordinate ring. -/
structure PunctureEvaluationData where
  evaluation : PunctureCoordinateRing S v →+* v.adicCompletion S.arithmetic.F
  evaluation_algebraMap :
    evaluation.comp (algebraMap (v.adicCompletion S.arithmetic.F)
      (PunctureCoordinateRing S v)) =
      RingHom.id (v.adicCompletion S.arithmetic.F)
  /-- Evaluation at the actual affine point. -/
  pointCoordinates : SourcePsiPunctureAffineCoordinates S v
  evaluation_eq : evaluation = punctureEvaluationOfCoordinates S v pointCoordinates

noncomputable def punctureEvaluationDataOfCoordinates
    (C : SourcePsiPunctureAffineCoordinates S v) :
    PunctureEvaluationData S v where
  evaluation := punctureEvaluationOfCoordinates S v C
  evaluation_algebraMap := punctureEvaluationOfCoordinates_algebraMap S v C
  pointCoordinates := C
  evaluation_eq := rfl

/-- The induced unit map to the completion field units. -/
noncomputable def punctureUnitMap
    (E : PunctureEvaluationData S v) :
    (PunctureCoordinateRing S v)ˣ →* (v.adicCompletion S.arithmetic.F)ˣ :=
  Units.map E.evaluation.toMonoidHom

theorem punctureUnitMap_constant
    (E : PunctureEvaluationData S v)
    (r : (v.adicCompletion S.arithmetic.F)ˣ) :
    punctureUnitMap S v E (Units.map
      (algebraMap (v.adicCompletion S.arithmetic.F)
        (PunctureCoordinateRing S v)).toMonoidHom r) = r := by
  ext
  have h := congrFun (congrArg DFunLike.coe E.evaluation_algebraMap)
    (r : v.adicCompletion S.arithmetic.F)
  simpa [punctureUnitMap] using h

theorem punctureUnitMap_surjective (E : PunctureEvaluationData S v) :
    Function.Surjective (punctureUnitMap S v E) := by
  intro r
  exact ⟨Units.map (algebraMap (v.adicCompletion S.arithmetic.F)
      (PunctureCoordinateRing S v)).toMonoidHom r,
    punctureUnitMap_constant S v E r⟩

/-- Affine coordinates from actual affine/integral puncture data. -/
noncomputable def coordinatesOfIntegralData
    (D : SourcePsiPunctureAffineIntegralData S v) :
    SourcePsiPunctureAffineCoordinates S v where
  x := algebraMap (v.adicCompletionIntegers S.arithmetic.F)
    (v.adicCompletion S.arithmetic.F) D.x
  y := algebraMap (v.adicCompletionIntegers S.arithmetic.F)
    (v.adicCompletion S.arithmetic.F) D.y
  nonsingular := D.nonsingular
  affine_eq := D.affine_eq

noncomputable def evaluationDataOfIntegralData
    (D : SourcePsiPunctureAffineIntegralData S v) : PunctureEvaluationData S v :=
  punctureEvaluationDataOfCoordinates S v (coordinatesOfIntegralData S v D)

/-- Affine/integral case: actual evaluation datum and surjective unit map. -/
theorem evaluation_and_surjective_of_integral
    (D : SourcePsiPunctureAffineIntegralData S v) :
    Nonempty (PunctureEvaluationData S v) ∧
      ∃ E : PunctureEvaluationData S v,
        Function.Surjective (punctureUnitMap S v E) :=
  ⟨⟨evaluationDataOfIntegralData S v D⟩,
    ⟨evaluationDataOfIntegralData S v D,
      punctureUnitMap_surjective S v (evaluationDataOfIntegralData S v D)⟩⟩

theorem not_affineCoordinates_of_atInfinity
    (hinf : sourcePunctureAffineLift S v = 0)
    (C : SourcePsiPunctureAffineCoordinates S v) : False := by
  have hsome := C.affine_eq
  rw [hinf] at hsome
  exact Option.noConfusion hsome

theorem not_evaluationData_of_atInfinity
    (hinf : sourcePunctureAffineLift S v = 0) :
    ¬ Nonempty (PunctureEvaluationData S v) := by
  rintro ⟨E⟩
  exact not_affineCoordinates_of_atInfinity S v hinf E.pointCoordinates

theorem not_affineIntegralData_of_coordinateNonintegral
    (C : SourcePsiPunctureAffineCoordinates S v)
    (hC : ¬ SourcePsiPunctureCoordinateIntegral S v C.x ∨
      ¬ SourcePsiPunctureCoordinateIntegral S v C.y) :
    ¬ Nonempty (SourcePsiPunctureAffineIntegralData S v) := by
  rintro ⟨D⟩
  have hx : algebraMap (v.adicCompletionIntegers S.arithmetic.F)
      (v.adicCompletion S.arithmetic.F) D.x = C.x := by
    have hsome := D.affine_eq
    rw [C.affine_eq] at hsome
    exact (Affine.Point.some.inj hsome).1
  have hy : algebraMap (v.adicCompletionIntegers S.arithmetic.F)
      (v.adicCompletion S.arithmetic.F) D.y = C.y := by
    have hsome := D.affine_eq
    rw [C.affine_eq] at hsome
    exact (Affine.Point.some.inj hsome).2
  rcases hC with hxbad | hybad
  · exact hxbad ⟨D.x, hx.symm⟩
  · exact hybad ⟨D.y, hy.symm⟩

/-- Exact evaluation trichotomy. -/
def SourcePsiEvaluationTrichotomy : Prop :=
  sourcePunctureAffineLift S v = 0 ∨
    (∃ C : SourcePsiPunctureAffineCoordinates S v,
      ¬ SourcePsiPunctureCoordinateIntegral S v C.x ∨
      ¬ SourcePsiPunctureCoordinateIntegral S v C.y) ∨
    (∃ E : PunctureEvaluationData S v,
      Function.Surjective (punctureUnitMap S v E))

theorem sourcePsiEvaluation_trichotomy :
    SourcePsiEvaluationTrichotomy S v := by
  classical
  rcases sourcePsiPuncture_trichotomy S v with hinf | hnon | hint
  · exact Or.inl hinf
  · exact Or.inr (Or.inl hnon)
  · rcases hint with ⟨D⟩
    exact Or.inr (Or.inr ⟨evaluationDataOfIntegralData S v D,
      punctureUnitMap_surjective S v (evaluationDataOfIntegralData S v D)⟩)

/-- In the affine-integral case, the actual evaluation and unit-map
surjectivity are obtained; in the other two cases they are obstructed. -/
theorem sourcePsiEvaluation_exact_dichotomy :
    (sourcePunctureAffineLift S v = 0 →
      ¬ Nonempty (PunctureEvaluationData S v)) ∧
    ((∃ C : SourcePsiPunctureAffineCoordinates S v,
        ¬ SourcePsiPunctureCoordinateIntegral S v C.x ∨
        ¬ SourcePsiPunctureCoordinateIntegral S v C.y) →
      ¬ Nonempty (SourcePsiPunctureAffineIntegralData S v)) ∧
    (Nonempty (SourcePsiPunctureAffineIntegralData S v) →
      ∃ E : PunctureEvaluationData S v,
        Function.Surjective (punctureUnitMap S v E)) :=
  ⟨fun hinf => not_evaluationData_of_atInfinity S v hinf,
    fun hnon => by
      rintro ⟨D⟩
      rcases hnon with ⟨C, hC⟩
      exact (not_affineIntegralData_of_coordinateNonintegral S v C hC) ⟨D⟩
    fun hint => by
      rcases hint with ⟨D⟩
      exact ⟨evaluationDataOfIntegralData S v D,
        punctureUnitMap_surjective S v (evaluationDataOfIntegralData S v D)⟩⟩

end LeanFormal.IUT.SourcePsiEvaluationDichotomy
end