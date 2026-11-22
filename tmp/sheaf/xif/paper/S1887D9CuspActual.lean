import tmp.sheaf.xif.paper.S1881D9D7bActual

/-!
# S1887: the actual D9 cusp origin from a boundary residual, and the exact first missing

S1881 isolates the two remaining D9 pairs.  For the cusp pair it constructs the
actual rank-one quotient `S1881ActualRankOneQuotient` from the large-image
input `hI` (the rank-two torsion basis of `E'`), proves its distinguished
class nonzero, and states the exact residual `S1881D9CuspMissing`: a rank-one
quotient together with a boundary residual `S1881CuspBoundaryResidual`, i.e.
a boundary cusp of the K-side orbicurve and an origin map on the nonzero
quotient classes.  The theorem `S1881CuspOrigin_of_actualResidual` consumes such
a residual; it does not construct one.

This file closes the *formal* gap exactly and isolates the geometric one.

## 1. The residual is exactly a boundary cusp

The frozen structure `S1881CuspBoundaryResidual` has three fields: the origin
map, the selected cusp, and the single equation saying that the origin map
sends the distinguished nonzero class to the selected cusp.  Nothing else is
required of the origin map.  Hence, over a fixed rank-one quotient `Q`,

    Nonempty (S1881CuspBoundaryResidual l (X := X) Q)  <->  Nonempty (OrbicurveBoundaryCusp X)

(`S1887CuspBoundaryResidual_nonempty_iff`).  The forward map is the cusp field;
the backward map uses the constant origin map at the given cusp.  So the
origin-map half of the D9 cusp datum carries no content beyond the cusp under
the current contract.  The paper's origin map (the bad-place local generator
±1, IUT I Definition 3.1(f) second half) is *not* what this contract records;
it remains the parked card IUT-I.definition-3.1-D9-cusp-local-generator.

## 2. The actual origin

`S1887ActualOrigin` is the actual `TorsionQuotientBoundaryOrigin l (S1732A l) X`
built from the actual S1881 quotient and an actual boundary cusp `c` of `X`:
its rank-one quotient is `S1881ActualRankOneQuotient l hI`, its cusp is `c`,
and its origin map is the constant map at `c`.  Its three frozen compatibilities
(origin equation, generator, nonzero) are proved, not assumed:

    S1887ActualOrigin_spec.

Consequently

    Nonempty (TorsionQuotientBoundaryOrigin l (S1732A l) X)  <->  Nonempty (OrbicurveBoundaryCusp X)

(`S1887CuspOrigin_nonempty_iff_cusp`): the whole D9 cusp origin slot is, under
the frozen contract, exactly one geometric object - a boundary cusp of the
K-side orbicurve.  This instantiates the hypothesis of
`S1881CuspOrigin_of_actualResidual` and hence fills the D9 cusp pair.

## 3. The D9 cusp pair

`S1887D9CuspPairOfCusp` is the D9 cusp `(Prop, proof)` pair `S1731D9CuspPair l`
whose proposition is the frozen candidate content
`ArithmeticCuspOriginCompatibility` of the actual origin.  Its proof is
`arithmeticCuspOriginCompatibility_of_supply`: the pair is filled as soon as a
boundary cusp is supplied.  Feeding it through S1881's assembly gives a full
`SourceDefinition31Data` (`S1887S1732SourceData`) conditional on exactly

    hI, G6, G7, D8 cusp clause, the D9 orbicurve slot, and one boundary cusp of C_K.

## 4. The exact first missing

    S1887D9CuspFirstMissing l S  :=  OrbicurveBoundaryCusp S.cK,

and `S1887D9CuspMissing_iff_cusp` proves

    S1881D9CuspMissing l S  <->  Nonempty (S1887D9CuspFirstMissing l S).

So the first missing datum is *one boundary cusp of the K-core orbicurve*.
Inside `OrbicurveBoundaryCusp` the first field is the compactification stack and
the first hard field is the representable open immersion
(`S1887BoundaryCuspEquivPrefixData` decomposes the structure into that prefix and
the boundary point data).  Neither is constructed anywhere in the tree: a
search of the whole repository finds `OrbicurveBoundaryCusp` only as a structure
and as a field, and no inhabitant of `EtaleStackRepresentableMorphismProperty`
(hence of `EtaleStackOpenImmersion`) - the representable open-immersion and full
2-pullback infrastructure is exactly the S1743/S1756/S1784/S1804/S1831 line,
still partially missing.  No cusp is manufactured here.

The actual S1726 orbicurve over the same field is *not* a substitute: it has the
once-punctured (1,1) signature, while the D9 K-core must have type (1,l-tors)^±;
`S1887D9CuspSlot_cK_ne_actualOrbicurve` proves `S.cK != S1726Orbicurve` (and
`S1887D9CuspSlot_cF_ne_actualOrbicurve` for C_F).  A boundary cusp of the actual
orbicurve would therefore be a cusp of a different orbicurve, not the D9 cusp of
C_K.

## 5. Honest boundary

At the level of the full Definition 3.1(f) source clause `SourceClauseF`
(SourceDefinition31Quantifiers.lean) three further obligations are *not*
covered by the D9 pair and are not touched here: the torsion-basis identity
`quotient_basis_eq_k_torsion_basis` against Clause (c)'s `k_torsion_basis`, the
identification `boundary_cusp_eq_epsilon` with the supplied geometric `epsilon`,
and the cuspidal decomposition datum `OrbicurveCuspidalDecompositionData` (which
itself contains a boundary cusp plus a closed decomposition subgroup of the
arithmetic profinite group).  The D9 pair built below is the S1731 frozen
`(Prop, proof)` pair, not the full clause (f).

No `True`, `PUnit`, arbitrary proposition, arbitrary group, `sorry`, `admit`, or
new axiom fills any field.  The only unfilled object is exposed as a type.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1887D9CuspActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1731D9PartialActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open CategoryTheory

universe u

variable (l : PrimeGeFive)

/-! ## 1. The boundary residual is exactly a boundary cusp -/

/-- The boundary residual determined by a boundary cusp over a fixed rank-one
quotient.  Its origin map is constant at the selected cusp; the frozen residual
contract imposes no other condition, so this is its general form. -/
def S1887ResidualOfCusp
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (Q : TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K))
    (c : Iut.OrbicurveBoundaryCusp X) :
    S1881CuspBoundaryResidual l (X := X) Q where
  originMap := fun _ => c
  cusp := c
  originMap_distinguishedClass := rfl

@[simp] theorem S1887ResidualOfCusp_cusp
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (Q : TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K))
    (c : Iut.OrbicurveBoundaryCusp X) :
    (S1887ResidualOfCusp l Q c).cusp = c := rfl

@[simp] theorem S1887ResidualOfCusp_originMap
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (Q : TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K))
    (c : Iut.OrbicurveBoundaryCusp X)
    (q : {q : Q.Quotient // q ≠ 0}) :
    (S1887ResidualOfCusp l Q c).originMap q = c := rfl

/-- The cusp of a boundary residual. -/
def S1887ResidualCusp
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    {Q : TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K)}
    (R : S1881CuspBoundaryResidual l (X := X) Q) :
    Iut.OrbicurveBoundaryCusp X :=
  R.cusp

@[simp] theorem S1887ResidualCusp_ofCusp
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (Q : TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K))
    (c : Iut.OrbicurveBoundaryCusp X) :
    S1887ResidualCusp l (S1887ResidualOfCusp l Q c) = c := rfl

/-- The residual's origin map sends the distinguished nonzero class to its
cusp.  This is the only equation the frozen contract records. -/
theorem S1887Residual_originMap_distinguished
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    {Q : TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K)}
    (R : S1881CuspBoundaryResidual l (X := X) Q) :
    R.originMap ⟨Q.distinguishedClass, Q.distinguishedClass_nonzero⟩ = R.cusp :=
  R.originMap_distinguishedClass

/-- **The boundary residual is exactly a boundary cusp**: over a fixed rank-one
quotient its nonemptiness is the nonemptiness of `OrbicurveBoundaryCusp X`. -/
theorem S1887CuspBoundaryResidual_nonempty_iff
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (Q : TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K)) :
    Nonempty (S1881CuspBoundaryResidual l (X := X) Q) ↔
      Nonempty (Iut.OrbicurveBoundaryCusp X) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.cusp⟩
  · rintro ⟨c⟩
    exact ⟨S1887ResidualOfCusp l Q c⟩

/-! ## 2. The actual origin over an actual boundary cusp -/

/-- **The actual D9 cusp origin**: the actual S1881 rank-one quotient together
with the constant origin map at an actual boundary cusp of the K-side
orbicurve.  No quotient, cusp value or equation is assumed. -/
noncomputable def S1887ActualOrigin
    (hI : S1725ImageContainsSL2 l)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (c : Iut.OrbicurveBoundaryCusp X) :
    TorsionQuotientBoundaryOrigin l (S1732A l) X where
  rank_one_quotient := S1881ActualRankOneQuotient l hI
  originMap := fun _ => c
  cusp := c
  originMap_distinguishedClass := rfl

@[simp] theorem S1887ActualOrigin_rank_one_quotient
    (hI : S1725ImageContainsSL2 l)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (c : Iut.OrbicurveBoundaryCusp X) :
    (S1887ActualOrigin l hI c).rank_one_quotient =
      S1881ActualRankOneQuotient l hI := rfl

@[simp] theorem S1887ActualOrigin_cusp
    (hI : S1725ImageContainsSL2 l)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (c : Iut.OrbicurveBoundaryCusp X) :
    (S1887ActualOrigin l hI c).cusp = c := rfl

@[simp] theorem S1887ActualOrigin_originMap
    (hI : S1725ImageContainsSL2 l)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (c : Iut.OrbicurveBoundaryCusp X) :
    (S1887ActualOrigin l hI c).originMap =
      fun _ => c := rfl

/-- The actual origin's origin map is constant at the selected cusp. -/
theorem S1887ActualOrigin_originMap_constant
    (hI : S1725ImageContainsSL2 l)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (c : Iut.OrbicurveBoundaryCusp X) :
    ∀ q, (S1887ActualOrigin l hI c).originMap q = c :=
  fun _ => rfl

/-- The three frozen compatibilities of the actual origin are proved facts: the
origin equation, the generator property, and the nonzeroness of the
distinguished class. -/
theorem S1887ActualOrigin_spec
    (hI : S1725ImageContainsSL2 l)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (c : Iut.OrbicurveBoundaryCusp X) :
    (S1887ActualOrigin l hI c).originMap
        (S1887ActualOrigin l hI c).distinguishedNonzeroClass =
        (S1887ActualOrigin l hI c).cusp ∧
      (S1887ActualOrigin l hI c).rank_one_quotient.quotientEquiv
          (S1887ActualOrigin l hI c).rank_one_quotient.distinguishedClass = 1 ∧
        (S1887ActualOrigin l hI c).rank_one_quotient.distinguishedClass ≠ 0 :=
  ⟨TorsionQuotientBoundaryOrigin.originMap_nonzeroClass_spec _,
    TorsionQuotientBoundaryOrigin.distinguishedClass_is_generator _,
    TorsionQuotientBoundaryOrigin.distinguishedClass_nonzero _⟩

/-- An actual boundary cusp fills the D9 cusp origin. -/
theorem S1887CuspOrigin_of_cusp
    (hI : S1725ImageContainsSL2 l)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (c : Iut.OrbicurveBoundaryCusp X) :
    Nonempty (TorsionQuotientBoundaryOrigin l (S1732A l) X) :=
  ⟨S1887ActualOrigin l hI c⟩

/-- Every D9 cusp origin exposes a boundary cusp of its K-side orbicurve. -/
def S1887CuspOrigin_cusp
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (O : TorsionQuotientBoundaryOrigin l (S1732A l) X) :
    Iut.OrbicurveBoundaryCusp X :=
  O.cusp

/-- **The whole D9 cusp origin slot is exactly one boundary cusp.** -/
theorem S1887CuspOrigin_nonempty_iff_cusp
    (hI : S1725ImageContainsSL2 l)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K} :
    Nonempty (TorsionQuotientBoundaryOrigin l (S1732A l) X) ↔
      Nonempty (Iut.OrbicurveBoundaryCusp X) := by
  constructor
  · rintro ⟨O⟩
    exact ⟨O.cusp⟩
  · rintro ⟨c⟩
    exact S1887CuspOrigin_of_cusp l hI c

/-! ## 3. The D9 cusp pair -/

/-- The D9 cusp `(Prop, proof)` pair of an actual boundary cusp.  Its content is
the frozen candidate statement `ArithmeticCuspOriginCompatibility` of the actual
origin, proved by `arithmeticCuspOriginCompatibility_of_supply`. -/
noncomputable def S1887D9CuspPairOfCusp
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (c : Iut.OrbicurveBoundaryCusp S.cK) :
    S1731D9CuspPair l where
  prop := ArithmeticCuspOriginCompatibility (S1887ActualOrigin l hI c)
  proof := arithmeticCuspOriginCompatibility_of_supply _

@[simp] theorem S1887D9CuspPairOfCusp_prop
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (c : Iut.OrbicurveBoundaryCusp S.cK) :
    (S1887D9CuspPairOfCusp l hI S c).prop =
      ArithmeticCuspOriginCompatibility (S1887ActualOrigin l hI c) := rfl

/-- The pair's proposition is the origin equation, the generator equation, and
the nonzeroness of the actual quotient: all three are proved without further
input. -/
theorem S1887D9CuspPairOfCusp_prop_spec
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (c : Iut.OrbicurveBoundaryCusp S.cK) :
    (S1887D9CuspPairOfCusp l hI S c).prop ↔
      ((S1887ActualOrigin l hI c).originMap
          (S1887ActualOrigin l hI c).distinguishedNonzeroClass =
          (S1887ActualOrigin l hI c).cusp ∧
        (S1887ActualOrigin l hI c).rank_one_quotient.quotientEquiv
            (S1887ActualOrigin l hI c).rank_one_quotient.distinguishedClass = 1 ∧
          (S1887ActualOrigin l hI c).rank_one_quotient.distinguishedClass ≠ 0) :=
  Iff.rfl

/-- An actual boundary cusp witnesses the exact S1881 missing statement at the
D9 orbicurve slot. -/
theorem S1887D9CuspMissing_of_cusp
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (c : Iut.OrbicurveBoundaryCusp S.cK) :
    S1881D9CuspMissing l S :=
  S1881D9CuspMissing_of_actualResidual l hI S (S1887ResidualOfCusp l _ c)

/-- Nonemptiness of the exact S1881 missing statement forces a boundary cusp of
the slot's K-core. -/
theorem S1887D9CuspMissing_cusp
    (S : S1881D9OrbicurveSlot l)
    (h : S1881D9CuspMissing l S) :
    Nonempty (Iut.OrbicurveBoundaryCusp S.cK) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨S1887ResidualCusp l hQ.some⟩

/-- **Exactness of the D9 cusp reduction.**  The S1881 missing statement is
exactly the existence of one boundary cusp of the slot's K-core. -/
theorem S1887D9CuspMissing_iff_cusp
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l) :
    S1881D9CuspMissing l S ↔
      Nonempty (Iut.OrbicurveBoundaryCusp S.cK) :=
  ⟨S1887D9CuspMissing_cusp l S, fun ⟨c⟩ => S1887D9CuspMissing_of_cusp l hI S c⟩

/-! ## 4. The exact first missing -/

/-- **The exact first missing field of the D9 cusp pair over the D9 orbicurve
slot**: a boundary cusp of the K-core orbicurve `S.cK`. -/
abbrev S1887D9CuspFirstMissing (S : S1881D9OrbicurveSlot l) : Type 1 :=
  Iut.OrbicurveBoundaryCusp S.cK

/-- The first missing type is exactly the S1881 missing statement. -/
theorem S1887D9CuspFirstMissing_iff
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l) :
    Nonempty (S1887D9CuspFirstMissing l S) ↔ S1881D9CuspMissing l S :=
  (S1887D9CuspMissing_iff_cusp l hI S).symm

/-- The exact first missing datum builds the D9 cusp origin over `S.cK`. -/
noncomputable def S1887D9CuspFirstMissing_origin
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    TorsionQuotientBoundaryOrigin l (S1732A l) S.cK :=
  S1887ActualOrigin l hI M

/-- The same datum builds the boundary residual at the actual rank-one
quotient. -/
def S1887D9CuspFirstMissing_residual
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    S1881CuspBoundaryResidual l (X := S.cK)
      (S1881ActualRankOneQuotient l hI) :=
  S1887ResidualOfCusp l _ M

/-- The exact first missing datum builds the D9 cusp pair of the slot. -/
noncomputable def S1887D9CuspPairOfMissing
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    S1731D9CuspPair l :=
  S1887D9CuspPairOfCusp l hI S M

/-! ## 5. Consumers: the S1881 D9 record and the S1732 source contract -/

/-- The two D9 pairs from the D9 orbicurve slot and one boundary cusp of its
K-core. -/
noncomputable def S1887D9MissingOfCusp
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    S1731D9Missing l :=
  S1881D9MissingOfData l S (S1887ActualOrigin l hI M)

@[simp] theorem S1887D9MissingOfCusp_orbicurve
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    (S1887D9MissingOfCusp l hI S M).orbicurve =
      S1881D9OrbicurvePairOfSlot l S := rfl

@[simp] theorem S1887D9MissingOfCusp_cusp
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    (S1887D9MissingOfCusp l hI S M).cusp =
      S1887D9CuspPairOfCusp l hI S M := rfl

/-- The actual D9 supply over the S1730 selection, conditional on `hI`, the D9
orbicurve slot, and one boundary cusp of its K-core. -/
noncomputable def S1887D9Supply
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    D9CompatibilitySupply :=
  S1881D9Supply l hI S (S1887ActualOrigin l hI M)

@[simp] theorem S1887D9Supply_cusp
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    (S1887D9Supply l hI S M).cusp =
      ArithmeticCuspOriginCompatibility (S1887ActualOrigin l hI M) := rfl

@[simp] theorem S1887D9Supply_orbicurve
    (hI : S1725ImageContainsSL2 l)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    (S1887D9Supply l hI S M).orbicurve = S1881D9OrbicurveMissing l := rfl

/-- The S1732 source contract with the D9 slot filled from the actual D9 orbicurve
slot and one boundary cusp of `S.cK`. -/
noncomputable def S1887S1732SourceData
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    SourceDefinition31Data.{0} l :=
  S1881S1732SourceData l hI G6 G7 Sc S (S1887ActualOrigin l hI M)

@[simp] theorem S1887S1732SourceData_cusp
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    (S1887S1732SourceData l hI G6 G7 Sc S M).arithmetic_cusp_compatibility =
      ArithmeticCuspOriginCompatibility (S1887ActualOrigin l hI M) := rfl

@[simp] theorem S1887S1732SourceData_orbicurve
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    (S1887S1732SourceData l hI G6 G7 Sc S M).arithmetic_orbicurve_compatibility =
      S1881D9OrbicurveMissing l := rfl

/-! ## 6. The actual S1726 orbicurve is not a substitute -/

/-- The D9 K-core orbicurve is not the actual S1726 orbicurve: their signatures
are different. -/
theorem S1887D9CuspSlot_cK_ne_actualOrbicurve
    (S : S1881D9OrbicurveSlot l) :
    S.cK ≠ S1726Orbicurve := by
  intro h
  have hs : S.cK.signature = S1726Orbicurve.signature :=
    congrArg (fun (X : Iut.HyperbolicOrbicurve (S1732A l).K) => X.signature) h
  rw [S.cK_signature, S1726Orbicurve_signature] at hs
  exact (S1881OncePunctured_ne_typeOneLTorsionPlusMinus l) hs.symm

/-- The F-side quotient of the D9 slot is not the actual S1726 orbicurve either. -/
theorem S1887D9CuspSlot_cF_ne_actualOrbicurve
    (S : S1881D9OrbicurveSlot l) :
    (S.cF : Iut.HyperbolicOrbicurve (S1732A l).K) ≠ S1726Orbicurve := by
  intro h
  have hs : S.cF.signature = S1726Orbicurve.signature :=
    congrArg (fun (X : Iut.HyperbolicOrbicurve (S1732A l).K) => X.signature) h
  rw [S.cF_signature, S1726Orbicurve_signature] at hs
  exact S1881OncePunctured_ne_typeOneOnePlusMinus hs.symm

/-! ## 7. What a boundary cusp still has to supply -/

/-- The compactification prefix of a boundary cusp: the first field is the
compactification stack, the first hard field the representable open
immersion. -/
structure S1887BoundaryCuspPrefix
    {F : Type u} [Field F] (X : Iut.HyperbolicOrbicurve F) where
  /-- The compactification stack. -/
  compactification : Iut.EtaleStackOverField F
  /-- The open morphism from the orbicurve to its compactification. -/
  openMap : X.stack.Hom compactification
  /-- It is representably an open immersion. -/
  openImmersion : Iut.EtaleStackOpenImmersion openMap

/-- The boundary point data of a boundary cusp over a given compactification
prefix: the residue scheme, the point of the compactification fiber, and the
separation of that point from the open orbicurve. -/
structure S1887BoundaryCuspPointData
    {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
    (P : S1887BoundaryCuspPrefix X) where
  /-- The residue scheme of the boundary point. -/
  residueScheme : Iut.SchemeOverField F
  /-- The point of the compactification fiber. -/
  point : Pseudofunctor.StrongTrans
    (Iut.schemeRepresentableEtalePseudofunctor F residueScheme)
    P.compactification.fiber
  /-- No point of the open orbicurve at the residue scheme is isomorphic to the
  boundary point. -/
  isBoundary : ∀ object :
      X.stack.fiber.obj (LocallyDiscrete.mk (Opposite.op residueScheme)),
      IsEmpty
        ((P.openMap.app
            (LocallyDiscrete.mk (Opposite.op residueScheme))).toFunctor.obj
              object ≅
          Iut.OrbicurveFiniteEtaleCover.pointObject residueScheme point)

/-- The compactification prefix of a boundary cusp. -/
def S1887BoundaryCuspPrefixOfCusp
    {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
    (C : Iut.OrbicurveBoundaryCusp X) : S1887BoundaryCuspPrefix X :=
  ⟨C.compactification, C.openMap, C.openImmersion⟩

/-- The first field of the prefix is the compactification stack of the cusp. -/
@[simp] theorem S1887BoundaryCuspPrefixOfCusp_compactification
    {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
    (C : Iut.OrbicurveBoundaryCusp X) :
    (S1887BoundaryCuspPrefixOfCusp C).compactification = C.compactification :=
  rfl

/-- The representable open immersion of the prefix is the cusp's open
immersion. -/
@[simp] theorem S1887BoundaryCuspPrefixOfCusp_openImmersion
    {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
    (C : Iut.OrbicurveBoundaryCusp X) :
    (S1887BoundaryCuspPrefixOfCusp C).openImmersion = C.openImmersion :=
  rfl

/-- **The boundary cusp is exactly its compactification prefix plus its boundary
point data.**  This is the field-level content of the first missing datum: a
compactification stack with a representable open immersion, and a boundary
point outside the open orbicurve. -/
noncomputable def S1887BoundaryCuspEquivPrefixData
    {F : Type u} [Field F] (X : Iut.HyperbolicOrbicurve F) :
    Iut.OrbicurveBoundaryCusp X ≃
      Σ P : S1887BoundaryCuspPrefix X, S1887BoundaryCuspPointData P where
  toFun C :=
    ⟨S1887BoundaryCuspPrefixOfCusp C,
      ⟨C.residueScheme, C.point, C.isBoundary⟩⟩
  invFun p :=
    { compactification := p.1.compactification
      openMap := p.1.openMap
      openImmersion := p.1.openImmersion
      residueScheme := p.2.residueScheme
      point := p.2.point
      isBoundary := p.2.isBoundary }
  left_inv C := by
    cases C
    rfl
  right_inv p := by
    rcases p with ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩
    rfl

/-- The first missing datum of the D9 cusp carries a compactification stack. -/
def S1887D9CuspFirstMissing_prefix
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    S1887BoundaryCuspPrefix S.cK :=
  S1887BoundaryCuspPrefixOfCusp M

@[simp] theorem S1887D9CuspFirstMissing_prefix_compactification
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    (S1887D9CuspFirstMissing_prefix l S M).compactification =
      M.compactification := rfl

@[simp] theorem S1887D9CuspFirstMissing_prefix_openImmersion
    (S : S1881D9OrbicurveSlot l)
    (M : S1887D9CuspFirstMissing l S) :
    (S1887D9CuspFirstMissing_prefix l S M).openImmersion =
      M.openImmersion := rfl

/-! ## 8. Axiom footprint -/

#print axioms S1887ResidualOfCusp
#print axioms S1887CuspBoundaryResidual_nonempty_iff
#print axioms S1887ResidualCusp
#print axioms S1887ActualOrigin
#print axioms S1887ActualOrigin_originMap_constant
#print axioms S1887ActualOrigin_spec
#print axioms S1887CuspOrigin_of_cusp
#print axioms S1887CuspOrigin_nonempty_iff_cusp
#print axioms S1887D9CuspPairOfCusp
#print axioms S1887D9CuspPairOfCusp_prop
#print axioms S1887D9CuspPairOfCusp_prop_spec
#print axioms S1887D9CuspMissing_of_cusp
#print axioms S1887D9CuspMissing_cusp
#print axioms S1887D9CuspMissing_iff_cusp
#print axioms S1887D9CuspFirstMissing
#print axioms S1887D9CuspFirstMissing_iff
#print axioms S1887D9CuspFirstMissing_origin
#print axioms S1887D9CuspFirstMissing_residual
#print axioms S1887D9CuspPairOfMissing
#print axioms S1887D9MissingOfCusp
#print axioms S1887D9Supply
#print axioms S1887S1732SourceData
#print axioms S1887S1732SourceData_cusp
#print axioms S1887D9CuspSlot_cK_ne_actualOrbicurve
#print axioms S1887D9CuspSlot_cF_ne_actualOrbicurve
#print axioms S1887BoundaryCuspEquivPrefixData
#print axioms S1887BoundaryCuspPrefixOfCusp_compactification
#print axioms S1887D9CuspFirstMissing_prefix_compactification

end LeanFormal.IUT.XiFPaper.S1887D9CuspActual
