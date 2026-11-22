import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual

noncomputable section
open LeanFormal.IUT
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.InitialThetaSource
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2906CorrectedDownstreamAuditAdapted

universe u

/-- The old strong unique field is false as soon as a nontrivial involution
exists: the identity is an involution with square one, so strong uniqueness
would force identity = ellipticInvolution. -/
theorem S2906_old_unique_false
    {F : Type u} [Field F]
    (xF : Iut.HyperbolicOrbicurve F)
    (e : xF.Hom xF)
    (hnt : e ≠ Iut.HyperbolicOrbicurve.Hom.id xF) :
    ¬ (∀ inv : xF.Hom xF,
        Iut.HyperbolicOrbicurve.Hom.TwoIso
          (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
          (Iut.HyperbolicOrbicurve.Hom.id xF) →
        inv = e) := by
  intro h
  have hsq : Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp
        (Iut.HyperbolicOrbicurve.Hom.id xF)
        (Iut.HyperbolicOrbicurve.Hom.id xF))
      (Iut.HyperbolicOrbicurve.Hom.id xF) := by
    change Iso ((𝟙 xF.stack.fiber) ≫ (𝟙 xF.stack.fiber)) (𝟙 xF.stack.fiber)
    exact eqToIso (Category.id_comp (𝟙 xF.stack.fiber))
  have h1 : Iut.HyperbolicOrbicurve.Hom.id xF = e :=
    h (Iut.HyperbolicOrbicurve.Hom.id xF) hsq
  exact hnt h1.symm

/-!
## S2906: downstream audit of old SourceSignQuotientData / SourceCompletion

### Old records and the false field

SourceSignQuotientGeometricCore (LeanFormal/IUTI/InitialTheta/
SourceSignQuotientConstruction.lean) contains the strong field

  unique_elliptic_involution :
    forall inv, TwoIso (comp inv inv) (Hom.id xF) -> inv = ellipticInvolution

This field is false whenever a nontrivial involution exists
(S2906_old_unique_false).  The corrected record
SourceSignQuotientDataCorrected (S2482CorrectedSourceSignQuotientActual)
replaces it by

  ellipticInvolution_nontrivial : ellipticInvolution != Hom.id xF
  unique_elliptic_involution :
    forall inv, TwoIso (comp inv inv) (Hom.id xF) ->
      inv != Hom.id xF -> Nonempty (TwoIso inv ellipticInvolution).

### Consumers of the old records

Direct builders of the old core (depend on the false strong unique field):
* S2850A6SignQuotientConditionalActual
* S2855A6CoreFromD6ConditionalActual
* S2856A6CoreWithInvolution
* S2859A6CoreActualInvolution
* S2860A6CoreWithSignActionConditional
* S2867A6CoreActualInvolutionSignAction

Consumers of old SourceSignQuotientData / old SourceCompletion:
* S2848A6CompletionConditionalActual
* S2858A6SFromCore
* S2859A6CoreActualInvolution (S2859Completion)
* S2860A6CoreWithSignActionConditional
* S2867A6CoreActualInvolutionSignAction
* S2869A6CoreWithGenericQuotient
* S2880CorrectedA6CoreNontrivialActual (corrected core, old completion through S2848)
* S2887CorrectedCoreMinimalActual (corrected core, old completion through S2848)
* S2892CoreWithQActual
* S2902CoreWithQMinimalActual

Files already using the corrected record:
* S2482CorrectedSourceSignQuotientActual (definition of corrected record)
* S2876CorrectedA6CoreActual
* S2880CorrectedA6CoreNontrivialActual
* S2887CorrectedCoreMinimalActual
* S2892CoreWithQActual
* S2902CoreWithQMinimalActual

### Precise corrected-version list needed

1. A corrected SourceCompletionCorrected (or a bridge from
   SourceSignQuotientDataCorrected to the old source, with the weakened unique
   field) is still missing.
2. The old SourceCompletion.ofSourceNative and SourceClauseConstructors still
   key on old SourceSignQuotientData; all clause A-F consumers therefore need
   a corrected bridge.
3. The downstream D7/D8/D9 consumers listed above need the corrected core;
   no corrected SourceCompletion exists yet.
4. S2848A6CompletionConditionalActual, S2858A6SFromCore and S2859/S2860/S2867
   completions are old-record consumers; they must be replayed against the
   corrected core or replaced by corrected completion wrappers.

No false strong-unique consumer is presented as finished.  No fake corrected
record is introduced here.
-/

#check @LeanFormal.IUT.InitialThetaSource.SourceSignQuotientGeometricCore.unique_elliptic_involution
#check LeanFormal.IUT.InitialThetaSource.SourceSignQuotientData
#check LeanFormal.IUT.InitialThetaSource.SourceCompletion
#check LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual.SourceSignQuotientDataCorrected
#check S2906_old_unique_false
#print axioms S2906_old_unique_false

end LeanFormal.IUT.XiFPaper.S2906CorrectedDownstreamAuditAdapted
end
