import tmp.sheaf.n8.closure.PaperInitialThetaData
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Constructed paper-to-current donors

Actual construction from SourceInitialThetaData clauses A/B:
- bad place subtype of actual VbadMod;
- bad lift to a finite place of F;
- actual stable and multiplicative reduction at the lift;
- actual real qParameter from ClauseB FinitePlaceQCandidate order.

Exact remaining donors: bad Fintype, labels, split-multiplicative card,
full torsion/orbicurve/sections/cusp clauses and the five compatibility
pairs.  No arbitrary fill.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.PaperToCurrentDonorsConstructed

universe u

variable {l : PrimeGeFive} (S : SourceInitialThetaData.{u} l)

abbrev PaperBadPlaces : Type u :=
  {p : NumberField.FinitePlace S.candidate.arithmetic.Fmod //
    p ∈ S.candidate.VbadMod}

abbrev PaperSelectedPlaces : Type u :=
  S.candidate.V

/-- The actual V <-> Fmod-place equivalence from the paper candidate. -/
noncomputable def paperPlaceEquiv :
    PaperSelectedPlaces S ≃ NumberFieldPlace S.candidate.arithmetic.Fmod :=
  Equiv.ofBijective S.candidate.placeToMod
    S.candidate.placeToMod_bijective

/-- Choose an actual finite F-place above a bad Fmod-place. -/
noncomputable def paperBadLift (b : PaperBadPlaces S) :
    NumberField.FinitePlace S.candidate.arithmetic.F :=
  (NumberFieldFinitePlace.comap_surjective
    (k := S.candidate.arithmetic.Fmod) (K := S.candidate.arithmetic.F)
    b.1).choose

theorem paperBadLift_comap (b : PaperBadPlaces S) :
    NumberFieldFinitePlace.comap (k := S.candidate.arithmetic.Fmod)
      (paperBadLift S b) = b.1 :=
  (NumberFieldFinitePlace.comap_surjective
    (k := S.candidate.arithmetic.Fmod) (K := S.candidate.arithmetic.F)
    b.1).choose_spec

def paperBadStable (b : PaperBadPlaces S) : Prop :=
  S.candidate.arithmetic.curve.HasStableReductionAt (paperBadLift S b)

theorem paperBadStable_proved (b : PaperBadPlaces S) :
    paperBadStable S b :=
  S.clauseA.stable_reduction_everywhere (paperBadLift S b)

def paperBadMultiplicative (b : PaperBadPlaces S) : Prop :=
  S.candidate.arithmetic.curve.HasMultiplicativeReductionAt (paperBadLift S b)

theorem paperBadMultiplicative_proved (b : PaperBadPlaces S) :
    paperBadMultiplicative S b :=
  S.clauseB.multiplicative_over_bad (paperBadLift S b) (by
    rw [paperBadLift_comap]
    exact b.2)

noncomputable def paperQCandidate (b : PaperBadPlaces S) :
    FinitePlaceQCandidate (paperBadLift S b) :=
  S.clauseB.qParameter (paperBadLift S b) (by
    rw [paperBadLift_comap]
    exact b.2)

noncomputable def paperQParameter (b : PaperBadPlaces S) : Real :=
  Real.exp (-((paperQCandidate S b).order : Real))

theorem paperQParameter_ne_zero (b : PaperBadPlaces S) :
    paperQParameter S b ≠ 0 :=
  Real.exp_ne_zero _

theorem paperQParameter_contracting (b : PaperBadPlaces S) :
    ‖paperQParameter S b‖ < 1 := by
  have hpos : 0 < ((paperQCandidate S b).order : Real) := by
    exact_mod_cast (paperQCandidate S b).order_pos
  have hneg : -((paperQCandidate S b).order : Real) < 0 := by linarith
  rw [paperQParameter, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
  exact Real.exp_lt_one_iff.mpr hneg

theorem paperQParameter_ne_one (b : PaperBadPlaces S) :
    paperQParameter S b ≠ 1 := by
  intro h
  have hExp : Real.exp (-((paperQCandidate S b).order : Real)) =
      Real.exp 0 := by simpa [paperQParameter] using h
  have harg := Real.exp_injective hExp
  have hpos : 0 < ((paperQCandidate S b).order : Real) := by
    exact_mod_cast (paperQCandidate S b).order_pos
  linarith

/-- Exact donors still needed for a full reduction clause. -/
structure PaperReductionDonors (S : SourceInitialThetaData.{u} l) where
  badFinite : Fintype (PaperBadPlaces S)
  selectedLabel : PaperSelectedPlaces S → Nat
  badLabel : PaperBadPlaces S → Nat
  label_compatible : ∀ b,
    selectedLabel (paperPlaceEquiv S |>.symm (NumberFieldPlace.finite b.1)) = badLabel b
  splitMultiplicativeReduction : ∀ b : PaperBadPlaces S,
    S.candidate.arithmetic.curve.HasSplitMultiplicativeReductionAt
      (paperBadLift S b)

/-- Actual reduction clause assembly from the donors; stable/multiplicative/q
are actual from clauses A/B. -/
noncomputable def paperReductionClause (D : PaperReductionDonors S) :
    SourceReductionClause (PaperSelectedPlaces S) (PaperBadPlaces S) where
  partition :=
    { badIncluded := fun b => (paperPlaceEquiv S).symm (NumberFieldPlace.finite b.1)
      selectedNonempty := by
        rcases S.clauseB.bad_nonempty with ⟨p, hp⟩
        exact ⟨(paperPlaceEquiv S).symm (NumberFieldPlace.finite p)⟩
      badFinite := D.badFinite
      selectedLabel := D.selectedLabel
      badLabel := D.badLabel
      badLabel_compatible := by
        intro b
        exact D.label_compatible b }
  stableReduction := fun b => paperBadStable S b
  stableReduction_proved := paperBadStable_proved S
  multiplicativeReduction := fun b => paperBadMultiplicative S b
  multiplicativeReduction_proved := paperBadMultiplicative_proved S
  splitMultiplicativeReduction := fun b =>
    S.candidate.arithmetic.curve.HasSplitMultiplicativeReductionAt
      (paperBadLift S b)
  splitMultiplicativeReduction_proved := D.splitMultiplicativeReduction
  reductionCompatibility := by
    intro b hb
    exact S.candidate.arithmetic.curve.hasSplitMultiplicativeReductionAt_imp_multiplicative
      (D.splitMultiplicativeReduction b)
  qParameter := paperQParameter S
  qParameter_nonzero := paperQParameter_ne_zero S
  qParameter_contracting := paperQParameter_contracting S
  qParameter_reduction_compatibility := by
    intro b _
    exact paperQParameter_ne_one S b

/-- Exact remaining clause donors after the actual reduction construction. -/
structure PaperRemainingClauseDonors (S : SourceInitialThetaData.{u} l) where
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

noncomputable def paperToCurrentDonors
    (R : PaperReductionDonors S) (C : PaperRemainingClauseDonors S) :
    PaperInitialThetaData.PaperToCurrentDonors S where
  reduction := paperReductionClause S R
  torsion := C.torsion
  orbicurve := C.orbicurve
  sections := C.sections
  cusp := C.cusp
  arithmetic_reduction_compatibility :=
    C.arithmetic_reduction_compatibility
  arithmetic_reduction_compatibility_proved :=
    C.arithmetic_reduction_compatibility_proved
  arithmetic_torsion_compatibility :=
    C.arithmetic_torsion_compatibility
  arithmetic_torsion_compatibility_proved :=
    C.arithmetic_torsion_compatibility_proved
  arithmetic_orbicurve_compatibility :=
    C.arithmetic_orbicurve_compatibility
  arithmetic_orbicurve_compatibility_proved :=
    C.arithmetic_orbicurve_compatibility_proved
  arithmetic_section_compatibility :=
    C.arithmetic_section_compatibility
  arithmetic_section_compatibility_proved :=
    C.arithmetic_section_compatibility_proved
  arithmetic_cusp_compatibility :=
    C.arithmetic_cusp_compatibility
  arithmetic_cusp_compatibility_proved :=
    C.arithmetic_cusp_compatibility_proved

noncomputable def paperSourceDefinition31Data
    (R : PaperReductionDonors S) (C : PaperRemainingClauseDonors S) :
    SourceDefinition31Data.{u} l :=
  PaperInitialThetaData.sourceDefinition31DataOfPaperDonors S
    (paperToCurrentDonors S R C)

end LeanFormal.IUT.N8Closure.PaperToCurrentDonorsConstructed

end