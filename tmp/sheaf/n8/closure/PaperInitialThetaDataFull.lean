import tmp.sheaf.n8.closure.PaperDonorsConstructed2

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Full paper initial Theta-data donor package

Bundles SourceInitialThetaData with the paper-qualified donor fields needed
for the current contract.  The assembly below uses actual arithmetic and
place carriers plus the actual reduction construction; no arbitrary
True/PUnit fill is performed.

Field-semantics gaps of the current shell clauses (documented, not hidden):
- orbicurve : SourceOrbicurveClause is a generic shell, not the paper
  SourceOrbicurveObject X_K/C_K; a paper-faithful input must supply the
  actual objects/morphisms, not a degenerate shell inhabitant.
- sections : SourceSectionClause lacks actual local-group section data;
  ClauseE local data is not converted here.
- cusp : SourceCuspClause uses Real epsilon/cuspScale, while the paper
  candidate carries epsilon in epsilonCarrier; no map is supplied.
The donors are therefore paper-qualified inputs, but the shell type
boundaries are not yet the paper objects.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.N8Closure.PaperInitialThetaDataFull

universe u

variable {l : PrimeGeFive}

/-- Paper source plus all donor/qualification fields needed to assemble the
current SourceDefinition31Data. -/
structure PaperInitialThetaDataFull (S : SourceInitialThetaData.{u} l) where
  /-- Paper-qualified bad-place finiteness card. -/
  badFinite : Fintype (PaperToCurrentDonorsConstructed.PaperBadPlaces S)
  /-- Place labels. -/
  selectedLabel : PaperToCurrentDonorsConstructed.PaperSelectedPlaces S → Nat
  badLabel : PaperToCurrentDonorsConstructed.PaperBadPlaces S → Nat
  label_compatible : ∀ b,
    selectedLabel
        ((PaperToCurrentDonorsConstructed.paperPlaceEquiv S).symm
          (NumberFieldPlace.finite b.1)) = badLabel b
  /-- Paper split-multiplicative reduction card. -/
  splitMultiplicativeReduction :
    ∀ b : PaperToCurrentDonorsConstructed.PaperBadPlaces S,
      S.candidate.arithmetic.curve.HasSplitMultiplicativeReductionAt
        (PaperToCurrentDonorsConstructed.paperBadLift S b)
  /-- Torsion shell donors. -/
  torsionLabel : PaperDonorsConstructed2.PaperTorsionCarrier S → Fin 6
  representation_surjective :
    Function.Surjective
      (PaperDonorsConstructed2.paperGaloisRepresentation S)
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  /-- Paper clause data for orbicurve/sections/cusp (current shell types). -/
  orbicurve : SourceOrbicurveClause.{u, u, u}
  sections : SourceSectionClause.{u, u, u}
  cusp : SourceCuspClause
  /-- Five compatibility source pairs. -/
  arithmetic_reduction_compatibility : Prop
  arithmetic_reduction_compatibility_proved :
    arithmetic_reduction_compatibility
  arithmetic_torsion_compatibility : Prop
  arithmetic_torsion_compatibility_proved :
    arithmetic_torsion_compatibility
  arithmetic_orbicurve_compatibility : Prop
  arithmetic_orbicurve_compatibility_proved :
    arithmetic_orbicurve_compatibility
  arithmetic_section_compatibility : Prop
  arithmetic_section_compatibility_proved :
    arithmetic_section_compatibility
  arithmetic_cusp_compatibility : Prop
  arithmetic_cusp_compatibility_proved :
    arithmetic_cusp_compatibility

namespace PaperInitialThetaDataFull

variable (S : SourceInitialThetaData.{u} l)
variable (F : PaperInitialThetaDataFull S)

/-- Actual reduction donors from the full package. -/
noncomputable def toReductionDonors :
    PaperToCurrentDonorsConstructed.PaperReductionDonors S where
  badFinite := F.badFinite
  selectedLabel := F.selectedLabel
  badLabel := F.badLabel
  label_compatible := F.label_compatible
  splitMultiplicativeReduction := F.splitMultiplicativeReduction

/-- Actual torsion donors from the full package. -/
noncomputable def toTorsionDonors :
    PaperDonorsConstructed2.PaperTorsionDonors S where
  torsionLabel := F.torsionLabel
  representation_surjective := F.representation_surjective
  sixTorsionIndependent := F.sixTorsionIndependent
  sixTorsionIndependent_proved := F.sixTorsionIndependent_proved

/-- Actual SourceTorsionClause assembled from ClauseC actual fields and the
torsion donors. -/
noncomputable def torsionClause : SourceTorsionClause.{u, u, u} l :=
  PaperDonorsConstructed2.paperTorsionClause S (toTorsionDonors S F)

/-- Remaining clause donors from the full package. -/
noncomputable def toRemainingClauseDonors :
    PaperToCurrentDonorsConstructed.PaperRemainingClauseDonors S where
  torsion := torsionClause S F
  orbicurve := F.orbicurve
  sections := F.sections
  cusp := F.cusp
  arithmetic_reduction_compatibility :=
    F.arithmetic_reduction_compatibility
  arithmetic_reduction_compatibility_proved :=
    F.arithmetic_reduction_compatibility_proved
  arithmetic_torsion_compatibility :=
    F.arithmetic_torsion_compatibility
  arithmetic_torsion_compatibility_proved :=
    F.arithmetic_torsion_compatibility_proved
  arithmetic_orbicurve_compatibility :=
    F.arithmetic_orbicurve_compatibility
  arithmetic_orbicurve_compatibility_proved :=
    F.arithmetic_orbicurve_compatibility_proved
  arithmetic_section_compatibility :=
    F.arithmetic_section_compatibility
  arithmetic_section_compatibility_proved :=
    F.arithmetic_section_compatibility_proved
  arithmetic_cusp_compatibility :=
    F.arithmetic_cusp_compatibility
  arithmetic_cusp_compatibility_proved :=
    F.arithmetic_cusp_compatibility_proved

/-- Actual assembly of the current SourceDefinition31Data from the full paper
package.  Arithmetic and V/Vbad carriers are actual; reduction is actual from
clauses A/B; torsion is actual from ClauseC plus donors; the remaining clauses
are the package's paper-qualified clause data. -/
noncomputable def toSourceDefinition31Data :
    SourceDefinition31Data.{u} l :=
  PaperInitialThetaData.sourceDefinition31DataOfPaperDonors S
    (PaperToCurrentDonorsConstructed.paperToCurrentDonors S
      (toReductionDonors S F) (toRemainingClauseDonors S F))

theorem toSourceDefinition31Data_arithmetic :
    (toSourceDefinition31Data S F).arithmetic = S.candidate.arithmetic :=
  rfl

end PaperInitialThetaDataFull

end LeanFormal.IUT.N8Closure.PaperInitialThetaDataFull

end