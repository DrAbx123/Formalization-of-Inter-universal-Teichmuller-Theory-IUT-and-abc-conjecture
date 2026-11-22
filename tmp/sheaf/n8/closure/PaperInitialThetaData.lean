import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Paper initial Theta-data projections

SourceInitialThetaData is the paper-faithful source candidate: actual place
sets, actual orbicurve objects over F/Fmod/K, and clauses A-F.  This file
provides the actual projections that are definitionally available and the
exact donor interface needed to assemble SourceDefinition31Data.  It does not
fabricate the mismatched shell fields.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.PaperInitialThetaData

universe u

variable {l : PrimeGeFive}

/-- Actual arithmetic root of the paper source candidate. -/
abbrev paperArithmetic (S : SourceInitialThetaData.{u} l) :
    InitialThetaArithmeticData.{u} l :=
  S.candidate.arithmetic

/-- Actual bad moduli set (finite places of Fmod). -/
abbrev paperVbadMod (S : SourceInitialThetaData.{u} l) :
    Set (NumberField.FinitePlace S.candidate.arithmetic.Fmod) :=
  S.candidate.VbadMod

/-- Actual selected moduli set. -/
abbrev paperVmod (S : SourceInitialThetaData.{u} l) :
    Set (NumberFieldPlace S.candidate.arithmetic.Fmod) :=
  S.candidate.Vmod

/-- Actual upstairs selected place carrier V. -/
abbrev paperV (S : SourceInitialThetaData.{u} l) : Type u :=
  S.candidate.V

/-- Actual place map V -> places of K. -/
abbrev paperPlace (S : SourceInitialThetaData.{u} l) :
    paperV S → NumberFieldPlace S.candidate.arithmetic.K :=
  S.candidate.place

/-- Actual restriction map V -> places of Fmod. -/
abbrev paperPlaceToMod (S : SourceInitialThetaData.{u} l) :
    paperV S → NumberFieldPlace S.candidate.arithmetic.Fmod :=
  S.candidate.placeToMod

theorem paperPlaceToMod_bijective (S : SourceInitialThetaData.{u} l) :
    Function.Bijective (paperPlaceToMod S) :=
  S.candidate.placeToMod_bijective

/-- Actual orbicurve objects xF, cF, xK, cK. -/
abbrev paperXF (S : SourceInitialThetaData.{u} l) :
    SourceOrbicurveObject S.candidate.arithmetic.F :=
  S.candidate.xF

abbrev paperCF (S : SourceInitialThetaData.{u} l) :
    SourceOrbicurveObject S.candidate.arithmetic.F :=
  S.candidate.cF

abbrev paperXK (S : SourceInitialThetaData.{u} l) :
    SourceOrbicurveObject S.candidate.arithmetic.K :=
  S.candidate.xK

abbrev paperCK (S : SourceInitialThetaData.{u} l) :
    SourceOrbicurveObject S.candidate.arithmetic.K :=
  S.candidate.cK

abbrev paperEpsilonCarrier (S : SourceInitialThetaData.{u} l) : Type u :=
  S.candidate.epsilonCarrier

abbrev paperEpsilon (S : SourceInitialThetaData.{u} l) :
    paperEpsilonCarrier S :=
  S.candidate.epsilon

/-- Exact donor interface for the fields that are not projections of the
paper candidate.  These are actual source clause objects, not arbitrary
fillers; no inhabitant is constructed here. -/
structure PaperToCurrentDonors (S : SourceInitialThetaData.{u} l) where
  reduction : SourceReductionClause (paperV S)
    {p : NumberField.FinitePlace S.candidate.arithmetic.Fmod //
      p ∈ S.candidate.VbadMod}
  torsion : SourceTorsionClause.{u, u, u} l
  orbicurve : SourceOrbicurveClause.{u, u, u}
  sections : SourceSectionClause.{u, u, u}
  cusp : SourceCuspClause
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

/-- Conditional assembly: actual arithmetic and actual V/Vbad carriers from
the paper candidate; remaining clause fields exactly from donors. -/
noncomputable def sourceDefinition31DataOfPaperDonors
    (S : SourceInitialThetaData.{u} l)
    (D : PaperToCurrentDonors S) :
    SourceDefinition31Data.{u} l where
  arithmetic := S.candidate.arithmetic
  selectedPlaces := paperV S
  badPlaces := {p : NumberField.FinitePlace S.candidate.arithmetic.Fmod //
    p ∈ S.candidate.VbadMod}
  reduction := D.reduction
  torsion := D.torsion
  orbicurve := D.orbicurve
  sections := D.sections
  cusp := D.cusp
  arithmetic_reduction_compatibility :=
    D.arithmetic_reduction_compatibility
  arithmetic_reduction_compatibility_proved :=
    D.arithmetic_reduction_compatibility_proved
  arithmetic_torsion_compatibility :=
    D.arithmetic_torsion_compatibility
  arithmetic_torsion_compatibility_proved :=
    D.arithmetic_torsion_compatibility_proved
  arithmetic_orbicurve_compatibility :=
    D.arithmetic_orbicurve_compatibility
  arithmetic_orbicurve_compatibility_proved :=
    D.arithmetic_orbicurve_compatibility_proved
  arithmetic_section_compatibility :=
    D.arithmetic_section_compatibility
  arithmetic_section_compatibility_proved :=
    D.arithmetic_section_compatibility_proved
  arithmetic_cusp_compatibility :=
    D.arithmetic_cusp_compatibility
  arithmetic_cusp_compatibility_proved :=
    D.arithmetic_cusp_compatibility_proved

theorem sourceDefinition31DataOfPaperDonors_arithmetic
    (S : SourceInitialThetaData.{u} l) (D : PaperToCurrentDonors S) :
    (sourceDefinition31DataOfPaperDonors S D).arithmetic =
      S.candidate.arithmetic := rfl

/-- Exact gap: no unconditional projection exists; the donor interface above
is the precise missing data. -/
def PaperToCurrentProjectionGap (S : SourceInitialThetaData.{u} l) : Prop :=
  ¬ Nonempty (PaperToCurrentDonors S)

end LeanFormal.IUT.N8Closure.PaperInitialThetaData

end