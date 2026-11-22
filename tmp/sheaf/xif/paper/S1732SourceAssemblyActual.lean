import tmp.sheaf.xif.paper.S1731D9PartialActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31PlacePartition

/-!
# S1732: the actual Definition 3.1 assembly over the S1724/S1730 source line

This file assembles the complete Definition 3.1 source contract
SourceDefinition31Data.{0} l for the actual paper arithmetic input

  A = S1724InitialThetaArithmeticData l

(A.Fmod = Q, A.F = A.K = F' = SplittingField (S1687H * (X^2 + 1)),
A.curve = E' = S1667Punctured.baseChange F'), with the actual S1730
bad-place data.

## The actual prefix (S1730, no extra condition)

* arithmetic := S1732A l = S1724InitialThetaArithmeticData l;
* selectedPlaces := Selected (S1730Selection l), S1730Selection l being
  the actual bad moduli set {3,5,7} \ {the place over l};
* badPlaces := Bad (S1730Selection l), with the finite instance proved in
  S1730;
* reduction := S1730SourceReductionClause l, the reduction-module assembly
  toSourceReductionClause (S1730Selection l) (S1730BadPlaceReductionCards l).
  Both the Clause (b) reduction cards and the Clause (c) q-parameter cards
  (S1730BadPlaceReductionCards l, S1730BadPlaceQParameterCards l) are
  actual and unconditional in S1730.

## The D5-D9 data (the exact condition boundary)

* D5: S1725SourceTorsionClause l hI, conditional on the explicit large-image
  source input hI : S1725ImageContainsSL2 l (S1725);
* D6: S1726SourceOrbicurveClauseOfGroupsAt S1726Orbicurve G6, conditional
  only on the certified orbifold fundamental-group datum
  G6 : Iut.OrbicurveFundamentalGroupData S1726Orbicurve
    (Iut.AbsoluteGaloisProfinite F') (S1726);
* D7: S1727SectionClause l G7, conditional only on the D7b local-group
  supply G7 : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l) (S1727);
* D8: a cusp clause Sc : SourceCuspClause supplied as input;
* D9: the five arithmetic-compatibility (Prop, proof) pairs.  The reduction,
  torsion, and sections pairs are the actual S1731 pairs
  (S1731D9ReductionProp l, S1731D9TorsionProp l hI,
  S1731D9SectionsProp l and their proofs); the orbicurve and cusp pairs are
  the two input pairs of M : S1731D9Missing l (S1731), never fabricated.

Thus the only non-actual inputs are

  hI, G6, G7, Sc, and the two D9 pairs in M.

No True, PUnit, arbitrary group, arbitrary proposition, sorry, admit,
or new axiom is used.

## Generic assembly

The assembly uses the generic Definition 3.1 entry
Definition31PlacePartition.d11EntryData (SourceDefinition31PlacePartition)
which is universe-polymorphic in A and takes an arbitrary
P : SourcePlaceSelection A.  It is not specialised to S1280Selection; the
generic entry is applied directly to S1730Selection l over
S1724InitialThetaArithmeticData l.  All projections are definitional (rfl).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.InitialThetaSource.Definition31PlacePartition
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1724PaperArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual
open LeanFormal.IUT.XiFPaper.S1730BadSetWithoutLActual
open LeanFormal.IUT.XiFPaper.S1731D9PartialActual

variable (l : PrimeGeFive)

/-! ## 1. The actual S1730 prefix over the S1724 arithmetic input -/

/-- The actual paper arithmetic input of S1724. -/
abbrev S1732A (l : PrimeGeFive) : InitialThetaArithmeticData.{0} l :=
  S1724InitialThetaArithmeticData l

/-- The actual S1730 source place selection over S1732A l. -/
abbrev S1732Selection (l : PrimeGeFive) :
    SourcePlaceSelection (S1732A l) :=
  S1730Selection l

/-- The selection is definitionally the S1730 selection. -/
theorem S1732Selection_eq_S1730 (l : PrimeGeFive) :
    S1732Selection l = S1730Selection l := rfl

/-- The actual S1730 Clause (b) reduction cards. -/
abbrev S1732ReductionCards (l : PrimeGeFive) :
    PlacePartitionReduction.BadPlaceReductionCards (S1732Selection l) :=
  S1730BadPlaceReductionCards l

/-- The actual S1730 Clause (c) q-parameter cards. -/
abbrev S1732QParameterCards (l : PrimeGeFive) :
    PlacePartitionReduction.BadPlaceQParameterCards (S1732Selection l) :=
  S1730BadPlaceQParameterCards l

/-- The actual D4 reduction clause over the S1730 selection. -/
abbrev S1732ReductionClause (l : PrimeGeFive) :
    SourceReductionClause (Selected (S1732Selection l))
      (Bad (S1732Selection l)) :=
  S1730SourceReductionClause l

/-! ## 2. The exact D6/D7 input types and the condition record -/

/-- The exact D6 input type of the task: the certified orbifold
fundamental-group datum of the actual S1726 hyperbolic orbicurve over the
absolute Galois group of F' = S1720Field. -/
abbrev S1732D6Input : Type 1 :=
  Iut.OrbicurveFundamentalGroupData S1726Orbicurve
    (Iut.AbsoluteGaloisProfinite S1720Field)

/-- The exact D7 input type of the task: the D7b local-group supply over the
canonical place-section layer S1727Layer l of the actual arithmetic input. -/
abbrev S1732D7Input (l : PrimeGeFive) : Type 1 :=
  D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)

/-- The D6 type is definitionally the S1726 S1726FirstMissing type. -/
theorem S1732D6Input_eq_S1726FirstMissing :
    S1732D6Input = S1726FirstMissing := rfl

/-- The D7 type is definitionally the S1727 S1727SectionFirstMissing type. -/
theorem S1732D7Input_eq_S1727FirstMissing (l : PrimeGeFive) :
    S1732D7Input l = S1727SectionFirstMissing l := rfl

/-- The exact non-actual condition record of the S1732 assembly.  Besides the
actual S1730 prefix, the construction consumes precisely these five fields.
No other source clause is an input. -/
structure S1732Conditions (l : PrimeGeFive) where
  /-- D5 large-image input of the actual E'/F' torsion clause. -/
  hI : S1725ImageContainsSL2 l
  /-- D6 orbifold fundamental-group datum of the actual S1726 orbicurve. -/
  G6 : S1732D6Input
  /-- D7b local-group supply over the canonical place-section layer. -/
  G7 : S1732D7Input l
  /-- D8 cusp clause, supplied as source input. -/
  cusp : SourceCuspClause
  /-- D9 orbicurve and cusp pairs, supplied as source input. -/
  D9 : S1731D9Missing l

/-! ## 3. The D5, D6, and D7 clauses from the actual constructions -/

/-- D5: the actual S1725 source-torsion clause, conditional on hI. -/
abbrev S1732D5Clause (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    SourceTorsionClause.{0, 0, 0} l :=
  S1725SourceTorsionClause l hI

/-- D6: the actual S1726 orbicurve clause of S1726Orbicurve, conditional on
the orbifold fundamental-group datum G6. -/
abbrev S1732D6Clause (G6 : S1732D6Input) :
    SourceOrbicurveClause.{0, 0, 0} :=
  S1726SourceOrbicurveClauseOfGroupsAt S1726Orbicurve G6

/-- D7: the actual S1727 place-section clause over S1727Layer l, conditional
on the D7b supply G7. -/
abbrev S1732D7Clause (l : PrimeGeFive) (G7 : S1732D7Input l) :
    SourceSectionClause.{0, 0, 0} :=
  S1727SectionClause l G7

/-- The D5 clause is definitionally the S1725 clause. -/
theorem S1732D5Clause_eq_S1725 (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    S1732D5Clause l hI = S1725SourceTorsionClause l hI := rfl

/-- The D6 clause is definitionally the S1726 clause at the actual orbicurve. -/
theorem S1732D6Clause_eq_S1726 (G6 : S1732D6Input) :
    S1732D6Clause G6 =
      S1726SourceOrbicurveClauseOfGroupsAt S1726Orbicurve G6 := rfl

/-- The D7 clause is definitionally the S1727 clause at the canonical layer. -/
theorem S1732D7Clause_eq_S1727 (l : PrimeGeFive) (G7 : S1732D7Input l) :
    S1732D7Clause l G7 = S1727SectionClause l G7 := rfl

/-! ## 4. The D9 pairs: three actual S1731 pairs and the two input pairs -/

/-- The D9 orbicurve pair of the input M. -/
abbrev S1732D9Orbicurve (l : PrimeGeFive) (M : S1731D9Missing l) :
    S1731D9OrbicurvePair l :=
  M.orbicurve

/-- The D9 cusp pair of the input M. -/
abbrev S1732D9Cusp (l : PrimeGeFive) (M : S1731D9Missing l) :
    S1731D9CuspPair l :=
  M.cusp

/-- The assembled D9 supply: the three actual S1731 pairs (reduction, torsion,
sections) together with the two input pairs of M (orbicurve, cusp).  This is
definitionally the S1731 completion S1731D9SupplyWithMissing. -/
noncomputable abbrev S1732D9Supply (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    D9CompatibilitySupply :=
  S1731D9SupplyWithMissing l hI M

/-- The D9 reduction pair is the actual S1731 pair. -/
theorem S1732D9Supply_reduction (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    (S1732D9Supply l hI M).reduction = S1731D9ReductionProp l := rfl

/-- The D9 torsion pair is the actual S1731 pair. -/
theorem S1732D9Supply_torsion (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    (S1732D9Supply l hI M).torsion = S1731D9TorsionProp l hI := rfl

/-- The D9 sections pair is the actual S1731 pair. -/
theorem S1732D9Supply_sections (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    (S1732D9Supply l hI M).sections = S1731D9SectionsProp l := rfl

/-- The D9 orbicurve pair is exactly the input pair. -/
theorem S1732D9Supply_orbicurve (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    (S1732D9Supply l hI M).orbicurve = M.orbicurve.prop := rfl

/-- The D9 cusp pair is exactly the input pair. -/
theorem S1732D9Supply_cusp (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    (S1732D9Supply l hI M).cusp = M.cusp.prop := rfl

/-- The D9 reduction slot is exactly the S1730 reduction and q-parameter
cards over the S1730 selection. -/
theorem S1732D9ReductionProp_eq (l : PrimeGeFive) :
    S1731D9ReductionProp l =
      ArithmeticReductionCompatibility (S1732Selection l)
        (S1732ReductionCards l) (S1732QParameterCards l) := rfl

/-- The D9 torsion slot is exactly the actual D5 clause. -/
theorem S1732D9TorsionProp_eq (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    S1731D9TorsionProp l hI =
      ArithmeticTorsionCompatibility (S1732D5Clause l hI) := rfl

/-- The D9 sections slot is exactly the S1730 selection condition. -/
theorem S1732D9SectionsProp_eq (l : PrimeGeFive) :
    S1731D9SectionsProp l =
      ArithmeticSectionCompatibility (S1732Selection l) := rfl

/-- The D9 supply is definitionally the S1731 completion of the three actual
pairs and the two input pairs. -/
theorem S1732D9Supply_eq (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    S1732D9Supply l hI M = S1731D9SupplyWithMissing l hI M := rfl

/-! ## 5. Assembly through the generic d11EntryData -/

/-- The actual Definition 3.1 source contract over A = S1732A l.

The generic entry Definition31PlacePartition.d11EntryData is applied directly
to P = S1730Selection l, C = S1730BadPlaceReductionCards l, the actual
D5/D6/D7 clauses, the input D8 cusp clause, and the five D9 pairs described
above.  It is not specialised to S1280Selection; the only hypotheses are
the five fields of S1732Conditions. -/
noncomputable def S1732SourceData (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    SourceDefinition31Data.{0} l :=
  d11EntryData (A := S1732A l) (S1730Selection l)
    (S1730BadPlaceReductionCards l)
    (S1725SourceTorsionClause l hI)
    (S1726SourceOrbicurveClauseOfGroupsAt S1726Orbicurve G6)
    (S1727SectionClause l G7)
    Sc
    (S1731D9ReductionProp l) (S1731D9Reduction_proved l)
    (S1731D9TorsionProp l hI) (S1731D9Torsion_proved l hI)
    M.orbicurve.prop M.orbicurve.proof
    (S1731D9SectionsProp l) (S1731D9Sections_proved l)
    M.cusp.prop M.cusp.proof

/-- The bundled form of the assembly: exactly the five conditions of
S1732Conditions produce the source contract. -/
noncomputable def S1732Conditions.toSourceData
    (C : S1732Conditions l) : SourceDefinition31Data.{0} l :=
  S1732SourceData l C.hI C.G6 C.G7 C.cusp C.D9

/-- The unbundled assembly is definitionally the bundled one. -/
theorem S1732SourceData_eq_toSourceData (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    S1732SourceData l hI G6 G7 Sc M =
      (⟨hI, G6, G7, Sc, M⟩ : S1732Conditions l).toSourceData := rfl

/-! ## 6. Projections of the assembled source contract (rfl) -/

@[simp] theorem S1732SourceData_arithmetic (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic = S1732A l :=
  rfl

@[simp] theorem S1732SourceData_selectedPlaces (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).selectedPlaces =
      Selected (S1730Selection l) :=
  rfl

@[simp] theorem S1732SourceData_badPlaces (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).badPlaces =
      Bad (S1730Selection l) :=
  rfl

@[simp] theorem S1732SourceData_reduction (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).reduction =
      S1730SourceReductionClause l :=
  rfl

@[simp] theorem S1732SourceData_torsion (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).torsion =
      S1725SourceTorsionClause l hI :=
  rfl

@[simp] theorem S1732SourceData_orbicurve (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).orbicurve =
      S1726SourceOrbicurveClauseOfGroupsAt S1726Orbicurve G6 :=
  rfl

@[simp] theorem S1732SourceData_sections (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).sections =
      S1727SectionClause l G7 :=
  rfl

@[simp] theorem S1732SourceData_cusp (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).cusp = Sc :=
  rfl

@[simp] theorem S1732SourceData_arithmetic_reduction_compatibility
    (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic_reduction_compatibility =
      S1731D9ReductionProp l :=
  rfl

@[simp] theorem S1732SourceData_arithmetic_reduction_compatibility_proved
    (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic_reduction_compatibility_proved =
      S1731D9Reduction_proved l :=
  rfl

@[simp] theorem S1732SourceData_arithmetic_torsion_compatibility
    (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic_torsion_compatibility =
      S1731D9TorsionProp l hI :=
  rfl

@[simp] theorem S1732SourceData_arithmetic_torsion_compatibility_proved
    (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic_torsion_compatibility_proved =
      S1731D9Torsion_proved l hI :=
  rfl

@[simp] theorem S1732SourceData_arithmetic_orbicurve_compatibility
    (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic_orbicurve_compatibility =
      M.orbicurve.prop :=
  rfl

@[simp] theorem S1732SourceData_arithmetic_orbicurve_compatibility_proved
    (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic_orbicurve_compatibility_proved =
      M.orbicurve.proof :=
  rfl

@[simp] theorem S1732SourceData_arithmetic_section_compatibility
    (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic_section_compatibility =
      S1731D9SectionsProp l :=
  rfl

@[simp] theorem S1732SourceData_arithmetic_section_compatibility_proved
    (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic_section_compatibility_proved =
      S1731D9Sections_proved l :=
  rfl

@[simp] theorem S1732SourceData_arithmetic_cusp_compatibility
    (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic_cusp_compatibility =
      M.cusp.prop :=
  rfl

@[simp] theorem S1732SourceData_arithmetic_cusp_compatibility_proved
    (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic_cusp_compatibility_proved =
      M.cusp.proof :=
  rfl

/-! ## 7. Projections to the Theorem 3.11 input (rfl) -/

@[simp] theorem S1732SourceData_initialTheta_arithmetic (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).toInitialThetaInput.arithmetic =
      S1732A l :=
  rfl

@[simp] theorem S1732SourceData_initialTheta_badPlaces (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).toInitialThetaInput.badPlaces =
      Bad (S1730Selection l) :=
  rfl

/-! ## 8. The exact condition boundary, recorded -/

/-- The prefix (arithmetic, selected places, bad places, reduction) is
independent of all five non-actual inputs: it is exactly the S1730 data.
This is the formal statement that no hidden condition enters the prefix. -/
theorem S1732SourceData_prefix_independent (l : PrimeGeFive)
    (hI₁ hI₂ : S1725ImageContainsSL2 l)
    (G6₁ G6₂ : S1732D6Input)
    (G7₁ G7₂ : S1732D7Input l)
    (Sc₁ Sc₂ : SourceCuspClause)
    (M₁ M₂ : S1731D9Missing l) :
    (S1732SourceData l hI₁ G6₁ G7₁ Sc₁ M₁).arithmetic =
        (S1732SourceData l hI₂ G6₂ G7₂ Sc₂ M₂).arithmetic ∧
      (S1732SourceData l hI₁ G6₁ G7₁ Sc₁ M₁).selectedPlaces =
        (S1732SourceData l hI₂ G6₂ G7₂ Sc₂ M₂).selectedPlaces ∧
      (S1732SourceData l hI₁ G6₁ G7₁ Sc₁ M₁).badPlaces =
        (S1732SourceData l hI₂ G6₂ G7₂ Sc₂ M₂).badPlaces ∧
      (S1732SourceData l hI₁ G6₁ G7₁ Sc₁ M₁).reduction =
        (S1732SourceData l hI₂ G6₂ G7₂ Sc₂ M₂).reduction :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The assembled contract has exactly the five supplied clause inputs.  This
records the condition boundary of S1732SourceData without introducing any
additional hypothesis. -/
theorem S1732SourceData_conditions (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (M : S1731D9Missing l) :
    (S1732SourceData l hI G6 G7 Sc M).arithmetic = S1732A l ∧
      (S1732SourceData l hI G6 G7 Sc M).torsion =
        S1725SourceTorsionClause l hI ∧
      (S1732SourceData l hI G6 G7 Sc M).orbicurve =
        S1726SourceOrbicurveClauseOfGroupsAt S1726Orbicurve G6 ∧
      (S1732SourceData l hI G6 G7 Sc M).sections =
        S1727SectionClause l G7 ∧
      (S1732SourceData l hI G6 G7 Sc M).cusp = Sc ∧
      (S1732SourceData l hI G6 G7 Sc M).arithmetic_orbicurve_compatibility =
        M.orbicurve.prop ∧
      (S1732SourceData l hI G6 G7 Sc M).arithmetic_cusp_compatibility =
        M.cusp.prop :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every choice of the five conditions produces an inhabitant of
SourceDefinition31Data.{0} l.  This is an existence statement for the
conditional assembly, not an assertion that the conditions themselves are
inhabited. -/
theorem S1732SourceData_nonempty (l : PrimeGeFive)
    (C : S1732Conditions l) :
    Nonempty (SourceDefinition31Data.{0} l) :=
  ⟨C.toSourceData⟩

/-- The bundled assembly is definitionally the unbundled one. -/
@[simp] theorem S1732Conditions.toSourceData_eq (l : PrimeGeFive)
    (C : S1732Conditions l) :
    C.toSourceData =
      S1732SourceData l C.hI C.G6 C.G7 C.cusp C.D9 :=
  rfl

/-! ## 9. Axiom footprint -/

#print axioms S1732SourceData
#print axioms S1732SourceData_arithmetic
#print axioms S1732SourceData_selectedPlaces
#print axioms S1732SourceData_badPlaces
#print axioms S1732SourceData_reduction
#print axioms S1732SourceData_torsion
#print axioms S1732SourceData_orbicurve
#print axioms S1732SourceData_sections
#print axioms S1732SourceData_cusp
#print axioms S1732SourceData_arithmetic_reduction_compatibility
#print axioms S1732SourceData_arithmetic_torsion_compatibility
#print axioms S1732SourceData_arithmetic_orbicurve_compatibility
#print axioms S1732SourceData_arithmetic_section_compatibility
#print axioms S1732SourceData_arithmetic_cusp_compatibility
#print axioms S1732SourceData_prefix_independent
#print axioms S1732SourceData_conditions
#print axioms S1732SourceData_nonempty
#print axioms S1732D9Supply
#print axioms S1732D9ReductionProp_eq
#print axioms S1732D9TorsionProp_eq
#print axioms S1732D9SectionsProp_eq
#print axioms S1732D9Supply_eq
#print axioms S1732D6Input_eq_S1726FirstMissing
#print axioms S1732D7Input_eq_S1727FirstMissing

end LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual

end
