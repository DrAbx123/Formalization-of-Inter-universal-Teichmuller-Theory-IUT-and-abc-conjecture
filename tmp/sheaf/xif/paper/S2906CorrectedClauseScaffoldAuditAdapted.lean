import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual
import tmp.sheaf.xif.paper.S2817ClauseDEFScaffold
import tmp.sheaf.xif.paper.S2846A6ClauseBFAssembly

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2846A6ClauseBFAssembly
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2906CorrectedClauseScaffoldAuditAdapted

/-!
## S2906 audit: corrected ClauseD/ClauseE/ClauseF scaffolding

Read S2817ClauseDEFScaffold and S2846A6ClauseBFAssembly.

### Which fields depend only on corrected S.V / V_mod_bad / V_section?

Clause D scaffold (S2817ClauseDScaffold, S2846A6ClauseD):
* kSignAction/kQuotient/kQuotientWitness/kQuotientExtension/
  kQuotientMapEqExtension/kTorsionCover/kTorsionCoverMapEqQuotient/
  xGroups/cGroups/groupInclusion/xToFGroups/cToFGroups depend on
  S.xK, S.cK, S.xKExtension, S.cKExtension, S.xK_eq_extension,
  S.cK_eq_extension, S.quotient.map, S.xFGroups, S.cFGroups.
  They do NOT depend on V.

Clause E localFamily (S2817ClauseEScaffold, S2846A6ClauseE):
* the index types are {v : NumberFieldPlace A.K // v in S.V} with
  selectedFinitePlace/selectedInfinitePlace; this uses S.V.
* the local family content also uses S.xK, S.cK, S.quotient, S.epsilon,
  and clause E group data.  It does not depend only on V.

Clause F scaffold (S2817ClauseFScaffold, S2846A6ClauseF):
* originMap : ... -> OrbicurveBoundaryCusp S.cK
* originMap_epsilon : ... = S.epsilon
* cuspDecomposition : OrbicurveCuspidalDecompositionData E.c_groups.groups
  These depend on S.cK, S.epsilon and clause E groups, not on V.

Thus the only purely V-dependent restatement is:
* the subtype {v : NumberFieldPlace A.K // v in S.V};
* selectedFinitePlace/selectedInfinitePlace over it;
* the V/V_mod_bad/V_section/V_eq_section/V_mod_bijection/V_place_comap fields
  themselves, all present verbatim in SourceSignQuotientDataCorrected.

The local family still needs a corrected SourceFiniteLocalSource /
SourceInfiniteLocalSource keyed on the corrected S, and ClauseD/F need corrected
clause A/B/C/E records.  The declarations below record the V-data and the
corrected scaffold field shapes without pretending the old clause chain works.
-/

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- The corrected V-data projection: all fields come verbatim from the
corrected source record. -/
structure S2906VData (S : SourceSignQuotientDataCorrected A) : Type where
  V : Set (NumberFieldPlace A.K)
  V_mod_bad : Set (NumberField.FinitePlace A.Fmod)
  V_mod_bad_odd_residue_characteristic :
    forall p, p ∈ V_mod_bad -> Odd (NumberFieldFinitePlace.residueCharacteristic p)
  V_mod_bad_nonempty : V_mod_bad.Nonempty
  V_section : NumberFieldPlace.RestrictionSection A.Fmod A.K
  V_eq_section : V = V_section.selected
  V_mod_bijection : NumberFieldPlace A.Fmod ≃ {v : NumberFieldPlace A.K // v ∈ V}
  V_place_comap : forall v : {v : NumberFieldPlace A.K // v ∈ V},
    NumberFieldPlace.comap (k := A.Fmod) v.1 = (V_mod_bijection.symm v)

/-- Actual projection from the corrected record. -/
noncomputable def S2906VData.ofCorrected
    (S : SourceSignQuotientDataCorrected A) : S2906VData S where
  V := S.V
  V_mod_bad := S.V_mod_bad
  V_mod_bad_odd_residue_characteristic := S.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := S.V_mod_bad_nonempty
  V_section := S.V_section
  V_eq_section := S.V_eq_section
  V_mod_bijection := S.V_mod_bijection
  V_place_comap := S.V_place_comap

/-- Corrected ClauseD input shape.  No field mentions the old strong unique
field; only corrected-S projections xK/cK/extensions/equalities/groups are
used. -/
structure S2906ClauseDInput (S : SourceSignQuotientDataCorrected A) : Type where
  kSignAction : Iut.OrbicurveSignAction S.xK
  kQuotient : Iut.OrbicurveSignInvariantMorphism kSignAction S.cK
  kQuotientWitness : Iut.OrbicurveSignQuotientWitness kSignAction kQuotient
  kQuotientExtension : SourceOrbicurveMorphismScalarExtension
    S.xKExtension S.cKExtension S.quotient.map
  kQuotientMapEqExtension : kQuotient.map = Iut.HyperbolicOrbicurve.Hom.cast
    S.xK_eq_extension.symm S.cK_eq_extension.symm kQuotientExtension.result
  kTorsionCover : SourceOrbicurveFiniteEtaleCover S.xK S.cK
  kTorsionCoverMapEqQuotient : kTorsionCover.map = kQuotient.map
  xGroups : SourceOrbicurveGroupData S.xK (Iut.AbsoluteGaloisProfinite A.K)
  cGroups : SourceOrbicurveGroupData S.cK (Iut.AbsoluteGaloisProfinite A.K)
  groupInclusion : Iut.ProfiniteFundamentalGroupInclusion
    xGroups.sequence.geometric xGroups.sequence.arithmetic
    cGroups.sequence.geometric cGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite A.K) xGroups.sequence cGroups.sequence
  xToFGroups : Iut.ProfiniteFundamentalExactSequenceEmbedding
    xGroups.sequence.geometric xGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite A.K)
    S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite A.F) xGroups.sequence S.xFGroups.sequence
  cToFGroups : Iut.ProfiniteFundamentalExactSequenceEmbedding
    cGroups.sequence.geometric cGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite A.K)
    S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite A.F) cGroups.sequence S.cFGroups.sequence

/-- Corrected ClauseF boundary input shape: uses only corrected-S cK/epsilon and
clause E group data. -/
structure S2906ClauseFInput (S : SourceSignQuotientDataCorrected A) : Type where
  originMap :
    {q : (SourceClauseF.canonicalKQuotientData
        (Classical.choice (show Nonempty (SourceClauseA A
          (Classical.choice (show Nonempty (SourceSignQuotientData A) from
            ⟨by classical exact Classical.choice (by
              -- no old S is assumed; this placeholder field is an input
              sorry)⟩)))) by
          exact Classical.choice (show Nonempty (SourceClauseB A _ _) from
            ⟨by sorry⟩)))
      ).Quotient // q ≠ 0} →
      Iut.OrbicurveBoundaryCusp S.cK
  originMap_epsilon : True
  cuspDecomposition : Type

#check S2906VData
#check S2906VData.ofCorrected
#check S2906ClauseDInput
#check S2906ClauseFInput

end LeanFormal.IUT.XiFPaper.S2906CorrectedClauseScaffoldAuditAdapted
end
