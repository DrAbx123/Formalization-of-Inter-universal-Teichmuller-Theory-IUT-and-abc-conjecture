import tmp.sheaf.xif.paper.S1730BadSetWithoutLActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import tmp.sheaf.xif.paper.S1727SectionsFPrimeActual

/-!
# S1731: the actual D9 pairs for reduction, torsion, and sections

The Definition 3.1 source contract carries five D9 arithmetic-compatibility
slots as opaque `(Prop, proof)` pairs (`SourceDefinition31Data`,
`SourceDefinition31Boundary.lean`:628-642; packaged as
`D9CompatibilitySupply`, `SourceDefinition31D4D9Supply.lean`:198-208).

This file constructs exactly three of those five pairs for the actual
arithmetic input and selection of the current source line:

* `A = S1724InitialThetaArithmeticData l` (S1724), so `A.Fmod = Q`,
  `A.F = A.K = F' = SplittingField (S1687H * (X^2 + 1))`, and
  `A.curve = E' = S1667Punctured.baseChange F'`;
* `P = S1730Selection l` (S1730), whose bad moduli set is
  `{3,5,7} \ {the place over l}` and whose `Bad P` index is finite;
* `C = S1730BadPlaceReductionCards l` and
  `Q = S1730BadPlaceQParameterCards l` (S1730), both unconditional.

The three constructed pairs are the concrete slot statements of
`SourceDefinition31ArithmeticCompatibilitySlots`:

1. reduction: `ArithmeticReductionCompatibility P C Q`, proved by
   `arithmeticReductionCompatibility_of_supply`; unconditional;
2. torsion: `ArithmeticTorsionCompatibility (S1725SourceTorsionClause l hI)`,
   proved by `arithmeticTorsionCompatibility_of_clause`; conditional on the
   explicit source input `hI : S1725ImageContainsSL2 l`, the large-image
   component of the actual E'/F' clause.  The other torsion components
   (six-torsion rationality, l-compatibility, `5 <= l`, `Odd l`) are actual;
   `S1731D9TorsionProp_iff_image` records that `hI` is the exact residual;
3. sections: `ArithmeticSectionCompatibility P`, proved by
   `arithmeticSectionCompatibility_canonical`; unconditional.  This is the
   place half of Definition 3.1(e) and depends only on the selection
   `SourcePlaceSelection` (through the canonical restriction section), not on
   the D7b local-group supply.  The full D7 clause `S1727SectionClause`
   remains conditional on `S1727SectionFirstMissing`; the canonical D7a
   layer `S1727Layer` is recorded below for comparison but is not consumed by
   the D9 sections pair.

The two remaining D9 pairs -- orbicurve and cusp -- are not constructed
here.  They are exposed as the explicit author-supplied pairs
`S1731D9OrbicurvePair` and `S1731D9CuspPair` in `S1731D9Missing`; no
`True`, `PUnit`, arbitrary group or arbitrary proposition is used as a
substitute.  The exact source boundary is recorded:

* orbicurve: S1726 constructs an actual hyperbolic orbicurve over the same
  `F' = A.K` with affine model E'; its D6 clause is still conditional on the
  certified orbifold fundamental-group data `S1726FirstMissing`, and no
  compiled proposition encodes the full D9 K-core identification.  The D9
  orbicurve pair therefore stays missing (parked card
  `IUT-I.definition-3.1-D9-orbicurve-slot`).
* cusp: the exact first field is a boundary origin
  `TorsionQuotientBoundaryOrigin l A X` over an actual K-core orbicurve
  `X`; the bad-place local-generator half remains the parked card
  `IUT-I.definition-3.1-D9-cusp-local-generator`.  No origin datum is
  manufactured.

The completion `S1731D9SupplyWithMissing` shows that the three actual pairs
plus the two missing pairs are exactly a `D9CompatibilitySupply`;
`S1731D9Supply_nonempty_iff_missing` records the corresponding
nonemptiness equivalence, and
`S1731D9SupplyWithMissing_eq_ofArithmeticSlots` shows that when the cusp
pair is the known global-origin candidate the completion is definitionally
the general constructor `D9CompatibilitySupply.ofArithmeticSlots`.

No sorry, no axiom, no admit, and no fabricated orbicurve/cusp pair.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1731D9PartialActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1724PaperArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual
open LeanFormal.IUT.XiFPaper.S1730BadSetWithoutLActual

variable {l : PrimeGeFive}

/-! ## 1. The actual D9 input -/

/-- The actual arithmetic input of the paper over F' (S1724). -/
abbrev S1731A (l : PrimeGeFive) : InitialThetaArithmeticData l :=
  S1724InitialThetaArithmeticData l

/-- The S1730 selection over `S1731A l`, with bad moduli set
`{3,5,7} \ {the place over l}`. -/
abbrev S1731Selection (l : PrimeGeFive) :
    SourcePlaceSelection (S1731A l) :=
  S1730Selection l

/-! ## 2. D9 reduction pair (actual, unconditional) -/

/-- The D9 `reduction` slot over the actual S1730 selection and cards. -/
def S1731D9ReductionProp (l : PrimeGeFive) : Prop :=
  ArithmeticReductionCompatibility (S1731Selection l)
    (S1730BadPlaceReductionCards l) (S1730BadPlaceQParameterCards l)

/-- The D9 reduction pair is actual: the reduction/coprimality cards are the
S1730 cards and the odd-residue/q-proxy conjuncts are proved facts. -/
theorem S1731D9Reduction_proved (l : PrimeGeFive) :
    S1731D9ReductionProp l :=
  arithmeticReductionCompatibility_of_supply
    (S1731Selection l) (S1730BadPlaceReductionCards l)
    (S1730BadPlaceQParameterCards l)

/-- The reduction Prop is definitionally the D9 slot statement. -/
theorem S1731D9ReductionProp_eq (l : PrimeGeFive) :
    S1731D9ReductionProp l =
      ArithmeticReductionCompatibility (S1731Selection l)
        (S1730BadPlaceReductionCards l) (S1730BadPlaceQParameterCards l) :=
  rfl

/-! ## 3. D9 torsion pair (actual, conditional on the image input hI) -/

/-- The D9 `torsion` slot of the actual E'/F' torsion clause, conditional on
the explicit large-image input `hI`. -/
def S1731D9TorsionProp (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) : Prop :=
  ArithmeticTorsionCompatibility (S1725SourceTorsionClause l hI)

/-- The D9 torsion pair is actual for every supplied image input `hI`. -/
theorem S1731D9Torsion_proved (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    S1731D9TorsionProp l hI :=
  arithmeticTorsionCompatibility_of_clause (S1725SourceTorsionClause l hI)

/-- The image input `hI` is the exact residual of the torsion pair: the other
three clause components are proved from the actual E'/F' data. -/
theorem S1731D9TorsionProp_iff_image (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    S1731D9TorsionProp l hI ↔ S1725ImageContainsSL2 l := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact S1731D9Torsion_proved l h

/-! ## 4. D9 sections pair (actual, unconditional)

The D9 sections statement is the place condition of Definition 3.1(e).  It
depends only on the `SourcePlaceSelection` (the canonical restriction
section), so it is unconditional.  The D7b local-group supply is not part of
the D9 pair. -/

/-- The D9 `sections` slot over the actual S1730 selection. -/
def S1731D9SectionsProp (l : PrimeGeFive) : Prop :=
  ArithmeticSectionCompatibility (S1731Selection l)

/-- The D9 sections pair is actual and unconditional. -/
theorem S1731D9Sections_proved (l : PrimeGeFive) :
    S1731D9SectionsProp l :=
  arithmeticSectionCompatibility_canonical (S1731Selection l)

/-- The canonical D7a place-section layer over the same arithmetic input
(S1727).  It is available unconditionally, but the D9 sections pair above
does not consume it: the D9 slot is already forced by the selection. -/
abbrev S1731D7Layer (l : PrimeGeFive) :
    SourceValuationSectionLayer (S1731A l) :=
  S1727Layer l

/-- The recorded D7 layer is exactly the generic canonical layer. -/
theorem S1731D7Layer_eq_canonical (l : PrimeGeFive) :
    S1731D7Layer l =
      SourceValuationSectionLayer.canonical (S1731A l) :=
  rfl

/-- D7a is available for every arithmetic input. -/
theorem S1731D7Layer_available (l : PrimeGeFive) :
    Nonempty (SourceValuationSectionLayer (S1731A l)) :=
  ⟨S1731D7Layer l⟩

/-- The exact first missing supply of the full D7 clause (S1727): the D7b
local-group supply.  It is not needed for the D9 sections pair. -/
abbrev S1731D7bMissing (l : PrimeGeFive) : Type 1 :=
  S1727SectionFirstMissing l

/-- The full D7 clause over the same arithmetic input, conditional on the
D7b supply (S1727).  It is recorded here only to separate the D7 residual
from the D9 sections pair, which does not consume it. -/
noncomputable abbrev S1731D7Clause (l : PrimeGeFive)
    (G : S1731D7bMissing l) : SourceSectionClause.{0, 0, 0} :=
  S1727SectionClause l G

/-- The full D7 clause exists for every supplied D7b supply. -/
theorem S1731D7Clause_nonempty (l : PrimeGeFive)
    (G : S1731D7bMissing l) :
    Nonempty (SourceSectionClause.{0, 0, 0}) :=
  ⟨S1731D7Clause l G⟩

/-! ## 5. The partial D9 record of the three actual pairs -/

/-- The three actual D9 `(Prop, proof)` pairs.  This is deliberately not a
`D9CompatibilitySupply`: the orbicurve and cusp pairs are absent. -/
structure S1731D9ThreeActual (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) where
  /-- D9 reduction slot. -/
  reduction : Prop
  reduction_proved : reduction
  /-- D9 torsion slot. -/
  torsion : Prop
  torsion_proved : torsion
  /-- D9 sections slot. -/
  sections : Prop
  sections_proved : sections

/-- The actual inhabitant of the partial D9 record. -/
noncomputable def S1731D9ThreeActual.actual (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    S1731D9ThreeActual l hI where
  reduction := S1731D9ReductionProp l
  reduction_proved := S1731D9Reduction_proved l
  torsion := S1731D9TorsionProp l hI
  torsion_proved := S1731D9Torsion_proved l hI
  sections := S1731D9SectionsProp l
  sections_proved := S1731D9Sections_proved l

@[simp] theorem S1731D9ThreeActual.actual_reduction (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    (S1731D9ThreeActual.actual l hI).reduction =
      S1731D9ReductionProp l := rfl

@[simp] theorem S1731D9ThreeActual.actual_reduction_proved
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1731D9ThreeActual.actual l hI).reduction_proved =
      S1731D9Reduction_proved l := rfl

@[simp] theorem S1731D9ThreeActual.actual_torsion (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    (S1731D9ThreeActual.actual l hI).torsion =
      S1731D9TorsionProp l hI := rfl

@[simp] theorem S1731D9ThreeActual.actual_torsion_proved
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1731D9ThreeActual.actual l hI).torsion_proved =
      S1731D9Torsion_proved l hI := rfl

@[simp] theorem S1731D9ThreeActual.actual_sections (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    (S1731D9ThreeActual.actual l hI).sections =
      S1731D9SectionsProp l := rfl

@[simp] theorem S1731D9ThreeActual.actual_sections_proved
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1731D9ThreeActual.actual l hI).sections_proved =
      S1731D9Sections_proved l := rfl

/-- The three actual pairs exist for every supplied image input. -/
theorem S1731D9ThreeActual.nonempty (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    Nonempty (S1731D9ThreeActual l hI) :=
  ⟨S1731D9ThreeActual.actual l hI⟩

/-! ## 6. The two exact missing D9 pairs -/

/-- The D9 `orbicurve` slot as an author-supplied `(Prop, proof)` pair.  No
proposition or proof is provided here.  The parked card
`IUT-I.definition-3.1-D9-orbicurve-slot` records the intended content; on
the object side S1726 constructs the actual hyperbolic orbicurve, while the
certified fundamental-group datum `S1726FirstMissing` and the D9 K-core
identification are still absent. -/
structure S1731D9OrbicurvePair (l : PrimeGeFive) : Type where
  prop : Prop
  proof : prop

/-- The D9 `cusp` slot as an author-supplied `(Prop, proof)` pair.  The exact
first field of its intended content is `S1731D9CuspFirstField`; the
bad-place local-generator half is the parked card
`IUT-I.definition-3.1-D9-cusp-local-generator`.  No pair is constructed. -/
structure S1731D9CuspPair (l : PrimeGeFive) : Type where
  prop : Prop
  proof : prop

/-- The exact missing part of D9: the orbicurve and cusp pairs. -/
structure S1731D9Missing (l : PrimeGeFive) : Type where
  orbicurve : S1731D9OrbicurvePair l
  cusp : S1731D9CuspPair l

/-- The actual K-core orbicurve object type of the arithmetic input.  S1726
constructs an actual orbicurve of this type over the same `F' = A.K`; this
alias records the object side only, not a D9 pair. -/
abbrev S1731D9OrbicurveObject (l : PrimeGeFive) : Type 1 :=
  Iut.HyperbolicOrbicurve (S1731A l).K

/-- The exact first field of the missing cusp pair: a boundary origin over an
actual K-core orbicurve. -/
abbrev S1731D9CuspFirstField (l : PrimeGeFive)
    (X : S1731D9OrbicurveObject l) : Type 1 :=
  TorsionQuotientBoundaryOrigin l (S1731A l) X

/-- Recover the missing pairs from an arbitrary D9 supply.  This is the
forward direction of the exactness statement for the supply interface; it
does not construct either pair. -/
def S1731D9Missing.ofSupply {l : PrimeGeFive}
    (S : D9CompatibilitySupply) : S1731D9Missing l where
  orbicurve := ⟨S.orbicurve, S.orbicurve_proved⟩
  cusp := ⟨S.cusp, S.cusp_proved⟩

/-! ## 7. Completion of the partial record and exactness -/

/-- The three actual pairs plus the two missing pairs are exactly a D9
supply.  The missing fields are copied from `M`; nothing is manufactured. -/
noncomputable def S1731D9SupplyWithMissing (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    D9CompatibilitySupply where
  reduction := S1731D9ReductionProp l
  reduction_proved := S1731D9Reduction_proved l
  torsion := S1731D9TorsionProp l hI
  torsion_proved := S1731D9Torsion_proved l hI
  orbicurve := M.orbicurve.prop
  orbicurve_proved := M.orbicurve.proof
  sections := S1731D9SectionsProp l
  sections_proved := S1731D9Sections_proved l
  cusp := M.cusp.prop
  cusp_proved := M.cusp.proof

@[simp] theorem S1731D9SupplyWithMissing_reduction (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    (S1731D9SupplyWithMissing l hI M).reduction =
      S1731D9ReductionProp l := rfl

@[simp] theorem S1731D9SupplyWithMissing_torsion (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    (S1731D9SupplyWithMissing l hI M).torsion =
      S1731D9TorsionProp l hI := rfl

@[simp] theorem S1731D9SupplyWithMissing_sections (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    (S1731D9SupplyWithMissing l hI M).sections =
      S1731D9SectionsProp l := rfl

@[simp] theorem S1731D9SupplyWithMissing_orbicurve (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    (S1731D9SupplyWithMissing l hI M).orbicurve =
      M.orbicurve.prop := rfl

@[simp] theorem S1731D9SupplyWithMissing_cusp (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (M : S1731D9Missing l) :
    (S1731D9SupplyWithMissing l hI M).cusp =
      M.cusp.prop := rfl

/-- Exactness of the completion: a D9 supply is the completion of the three
actual pairs and some missing pairs precisely when its reduction, torsion,
and sections slots are the actual ones. -/
theorem S1731D9SupplyWithMissing_eq_iff (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (S : D9CompatibilitySupply) :
    (∃ M : S1731D9Missing l, S1731D9SupplyWithMissing l hI M = S) ↔
      S.reduction = S1731D9ReductionProp l ∧
        S.torsion = S1731D9TorsionProp l hI ∧
          S.sections = S1731D9SectionsProp l := by
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · intro h
    cases S with
    | mk red redp tor torp orb orbp sec secp cus cusp =>
      obtain ⟨hred, htor, hsec⟩ := h
      refine ⟨⟨⟨orb, orbp⟩, ⟨cus, cusp⟩⟩, ?_⟩
      subst hred
      subst htor
      subst hsec
      rfl

/-- With the three actual pairs fixed, the D9 supply interface has exactly
the two missing pairs as residual input. -/
theorem S1731D9Supply_nonempty_iff_missing (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    Nonempty D9CompatibilitySupply ↔ Nonempty (S1731D9Missing l) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S1731D9Missing.ofSupply S⟩
  · rintro ⟨M⟩
    exact ⟨S1731D9SupplyWithMissing l hI M⟩

/-- When the cusp pair is the known global-origin candidate
`ArithmeticCuspOriginCompatibility O`, the completion is definitionally the
general constructor `D9CompatibilitySupply.ofArithmeticSlots` applied to the
actual selection, cards, torsion clause, and the supplied orbicurve pair.
The origin `O` is not constructed here. -/
theorem S1731D9SupplyWithMissing_eq_ofArithmeticSlots (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    {X : S1731D9OrbicurveObject l}
    (O : TorsionQuotientBoundaryOrigin l (S1731A l) X)
    (orbicurve : Prop) (orbicurve_proved : orbicurve) :
    S1731D9SupplyWithMissing l hI
      { orbicurve := ⟨orbicurve, orbicurve_proved⟩
        cusp :=
          ⟨ArithmeticCuspOriginCompatibility O,
            arithmeticCuspOriginCompatibility_of_supply O⟩ } =
      D9CompatibilitySupply.ofArithmeticSlots
        (T := S1725SourceTorsionClause l hI)
        (S1730Selection l) (S1730BadPlaceReductionCards l)
        (S1730BadPlaceQParameterCards l) O orbicurve orbicurve_proved :=
  rfl

/-! ## 8. Axiom footprint -/

#print axioms S1731D9Reduction_proved
#print axioms S1731D9Torsion_proved
#print axioms S1731D9TorsionProp_iff_image
#print axioms S1731D9Sections_proved
#print axioms S1731D7Layer_eq_canonical
#print axioms S1731D7Layer_available
#print axioms S1731D7Clause
#print axioms S1731D7Clause_nonempty
#print axioms S1731D9ThreeActual.actual
#print axioms S1731D9ThreeActual.nonempty
#print axioms S1731D9Missing.ofSupply
#print axioms S1731D9SupplyWithMissing
#print axioms S1731D9SupplyWithMissing_eq_iff
#print axioms S1731D9Supply_nonempty_iff_missing
#print axioms S1731D9SupplyWithMissing_eq_ofArithmeticSlots

end LeanFormal.IUT.XiFPaper.S1731D9PartialActual

end
