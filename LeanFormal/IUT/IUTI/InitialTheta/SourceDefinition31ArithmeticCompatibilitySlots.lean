/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31PlacePartition
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionRankOneQuotient
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

/-!
# IUT I Definition 3.1: concrete candidates for the five D9 arithmetic
compatibility slots

Frozen scope (2026-10-16, `estimates-rec8` D3.1 item 22, D5-D9 chain).

The five D9 arithmetic-compatibility slots of `SourceDefinition31Data`
(`SourceDefinition31Boundary.lean`:669-682) are opaque `(Prop, proof)`
pairs supplied by the instance author; `D9CompatibilitySupply`
(`SourceDefinition31D4D9Supply.lean`:183-193) packages them, and
`d11EntryData` (`SourceDefinition31PlacePartition.lean`:180) consumes
them as explicit hypotheses.  This module freezes, for each slot, the
paper condition that the slot is meant to record, and proves the
concrete instance wherever the current interfaces support it.

Paper anchors (corpus `Inter-universal Teichmuller Theory I.txt`):

* reduction: Definition 3.1(b)-(c), lines 3131-3184 - bad
  (multiplicative) reduction at places over V^bad_mod, nonempty
  odd-residue bad-moduli set, `l` prime to the bad residue
  characteristics and to the q-parameter orders;
* torsion: Definition 3.1(b)-(c), lines 3174-3184 - 2*3-torsion
  rational over F, image of G_F -> GL_2(F_l) containing SL_2(F_l),
  K the kernel field;
* orbicurve: Definition 3.1(d), lines 3185-3215 - parked; the actual
  K-core orbicurve C_K = C_F x_F K with certified etale fundamental
  groups is a source object that no compiled supplier constructs
  (see the card `IUT-I.definition-3.1-D9-orbicurve-slot`);
* sections: Definition 3.1(e), lines 3216-3226 - V a subset of V(K)
  inducing a natural bijection V ~ V_mod (a section of
  V(K) ->> V_mod), with the V_non/V_arc and V_bad/V_good
  decompositions;
* cusp: Definition 3.1(f), lines 3273-3295 - the cusp arising from a
  nonzero element of the quotient Q; the compiled global algebraic
  origin is frozen here, the local generator condition at bad places
  is parked (see the card
  `IUT-I.definition-3.1-D9-cusp-local-generator`).

Honest scope.  The reduction statement is assembled from the supplied
cards `BadPlaceReductionCards` / `BadPlaceQParameterCards` plus the
already-proved `badPlaceQProxy` facts and the selection's odd-residue
field; the section statement is assembled from already-proved
`SourcePlaceSelection` lemmas (with two new derived lemmas below); the
torsion statement projects the clause fields, and the Serre large-image
content stays the existing research-level card
`IUT-I.elliptic-l-torsion-large-image`; the cusp statement is the
global algebraic origin recorded by `TorsionQuotientBoundaryOrigin`.
No source condition is manufactured, and no gate
(`D9CompatibilityConstruction` / `D10InitialThetaConstruction`) is
closed: the D9 supply wiring (consumer side, in `SourceDefinition31D4D9Supply.lean`)
still takes the orbicurve slot as an explicit hypothesis.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace LeanFormal.IUT

noncomputable section

universe u v w

namespace InitialThetaSource

open PlacePartitionReduction

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-! ## Slot 1: reduction and arithmetic compatibility -/

/-- Frozen candidate content of the D9 `reduction` slot: the
Definition 3.1(b) reduction conditions at every bad moduli place
together with the Definition 3.1(c) coprimalities.  The reduction and
coprimality cards remain hypotheses (source inputs); the odd-residue
and q-proxy conjuncts are the already available derived facts. -/
def ArithmeticReductionCompatibility (P : SourcePlaceSelection A)
    [Fintype (Bad P)] (C : BadPlaceReductionCards P)
    (Q : BadPlaceQParameterCards P) : Prop :=
  (∀ p : NumberField.FinitePlace A.Fmod, p ∈ P.V_mod_bad →
      Odd (NumberFieldFinitePlace.residueCharacteristic p) ∧
        Nat.Coprime (NumberFieldFinitePlace.residueCharacteristic p)
          l.value) ∧
    (∀ b : Bad P,
      HasStableReductionOver P b ∧
        HasMultiplicativeReductionOver P b ∧
          HasSplitMultiplicativeReductionOver P b) ∧
    (∀ b : Bad P,
      (toSourceReductionClause P C).qParameter b ≠ 0 ∧
        ‖(toSourceReductionClause P C).qParameter b‖ < 1 ∧
          (toSourceReductionClause P C).qParameter b ≠ 1) ∧
    (∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime (Q.sourceQParameterOrder w hw) l.value)

/-- The reduction slot statement holds for every supplied selection and
card pair: the arithmetic content is exactly the supplied cards plus
the selection's odd-residue field, and the q-proxy conjuncts are the
already-proved `badPlaceQProxy` facts. -/
theorem arithmeticReductionCompatibility_of_supply
    (P : SourcePlaceSelection A) [Fintype (Bad P)]
    (C : BadPlaceReductionCards P) (Q : BadPlaceQParameterCards P) :
    ArithmeticReductionCompatibility P C Q :=
  ⟨fun p hp =>
      ⟨P.V_mod_bad_odd_residue_characteristic p hp,
        Q.badResidueCharacteristic_primeToL p hp⟩,
    fun b =>
      ⟨hasStableReductionOver_of_cards P C b,
        hasMultiplicativeReductionOver_of_cards P C b,
        hasSplitMultiplicativeReductionOver_of_cards P C b⟩,
    fun b =>
      ⟨show badPlaceQProxy P b ≠ 0 from badPlaceQProxy_ne_zero P b,
        show ‖badPlaceQProxy P b‖ < 1 from
          badPlaceQProxy_norm_lt_one P b,
        show badPlaceQProxy P b ≠ 1 from badPlaceQProxy_ne_one P b⟩,
    fun w hw => Q.sourceQParameterOrder_primeToL w hw⟩

/-! ## Slot 2: torsion and arithmetic compatibility -/

/-- Frozen candidate content of the D9 `torsion` slot: the compiled
paragraph-(c) content of the torsion clause together with the prime
label arithmetic.  The large-image component is the clause field; the
research-level Serre card `IUT-I.elliptic-l-torsion-large-image` stays
open, and this statement is not a substitute for it. -/
def ArithmeticTorsionCompatibility
    (T : Theorem311Source.SourceTorsionClause.{u, v, w} l) : Prop :=
  T.imageContainsSL2 ∧ T.sixTorsionIndependent ∧
    T.lTorsionCompatible ∧ 5 ≤ l.value ∧ Odd l.value

/-- The torsion slot statement projects the supplied clause fields and
derives `5 <= l` and `Odd l` from the prime label record. -/
theorem arithmeticTorsionCompatibility_of_clause
    (T : Theorem311Source.SourceTorsionClause.{u, v, w} l) :
    ArithmeticTorsionCompatibility T :=
  ⟨T.imageContainsSL2_proved, T.sixTorsionIndependent_proved,
    T.lTorsionCompatible_proved, l.ge_five, l.odd⟩

/-! ## Slot 4: place sections and arithmetic compatibility -/

/-- Frozen candidate content of the D9 `sections` slot: the
Definition 3.1(e) place condition - the selected set `V` of `V(K)`
induces a natural bijection with `V_mod` (a section of the restriction
`V(K) ->> V_mod`), with the `V_non/V_arc` and `V_bad/V_good`
decompositions and the bad-fibre identification. -/
def ArithmeticSectionCompatibility (P : SourcePlaceSelection A) : Prop :=
  Nonempty
      (NumberFieldPlace A.Fmod ≃
        {v : NumberFieldPlace A.K // v ∈ P.V}) ∧
    (∀ v : NumberFieldPlace A.Fmod,
      NumberFieldPlace.comap (k := A.Fmod) (P.V_section.lift v) = v) ∧
    Function.Injective P.V_section.lift ∧
    (∀ v : {v : NumberFieldPlace A.K // v ∈ P.V},
      NumberFieldPlace.comap (k := A.Fmod) v.1 =
        P.V_mod_bijection.symm v) ∧
    P.V_bad ∪ P.V_good = Set.univ ∧
    Disjoint P.V_bad P.V_good ∧
    P.V_non ∪ P.V_arc = Set.univ ∧
    Disjoint P.V_non P.V_arc ∧
    (P.V_bad).Nonempty ∧
    (∀ v : {v : NumberFieldPlace A.K // v ∈ P.V},
      v ∈ P.V_bad ↔
        NumberFieldPlace.comap (k := A.Fmod) v.1 ∈
          NumberFieldPlace.finite '' P.V_mod_bad)

/-- The bad-selected places are exactly the places of `V` whose
restriction to `Fmod` lies over `V^bad_mod`. -/
theorem V_bad_iff_comap_mem (P : SourcePlaceSelection A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.V}) :
    v ∈ P.V_bad ↔
      NumberFieldPlace.comap (k := A.Fmod) v.1 ∈
        NumberFieldPlace.finite '' P.V_mod_bad := by
  rw [P.V_bad_finite_spec v, ← P.V_place_comap v]

/-- Every moduli place has a selected place above it: the restriction
map restricted to `V` is surjective onto `V_mod`. -/
theorem selected_place_surjects (P : SourcePlaceSelection A)
    (v : NumberFieldPlace A.Fmod) :
    ∃ w : {w : NumberFieldPlace A.K // w ∈ P.V},
      NumberFieldPlace.comap (k := A.Fmod) w.1 = v :=
  ⟨P.V_mod_bijection v, by
    rw [P.V_place_comap (P.V_mod_bijection v)]
    exact P.selected_equiv_left_inverse v⟩

/-- The section slot statement holds canonically for every supplied
selection: the place half of Definition 3.1(e) is carried by the
canonical restriction section and the proved place lemmas. -/
theorem arithmeticSectionCompatibility_canonical
    (P : SourcePlaceSelection A) :
    ArithmeticSectionCompatibility P :=
  ⟨⟨P.V_mod_bijection⟩,
    P.selected_place_comap_left_inverse,
    P.selected_place_lift_injective,
    P.V_place_comap,
    P.V_bad_or_good_cover,
    P.V_bad_or_good_disjoint,
    P.V_non_or_arc_cover,
    P.V_non_or_arc_disjoint,
    P.V_bad_nonempty,
    V_bad_iff_comap_mem P⟩

/-! ## Slot 5: cusp origin and arithmetic compatibility -/

/-- Frozen candidate content of the D9 `cusp` slot, global algebraic
origin half: the boundary cusp is the image of the canonical generator
class of the rank-one quotient under the supplied origin map.  The
domain `{q // q ≠ 0}` is the nonzero quotient of Definition 3.1(f);
the local generator condition at bad places is not part of this
statement (see the card
`IUT-I.definition-3.1-D9-cusp-local-generator`). -/
def ArithmeticCuspOriginCompatibility {X : Iut.HyperbolicOrbicurve A.K}
    (O : TorsionQuotientBoundaryOrigin l A X) : Prop :=
  O.originMap O.distinguishedNonzeroClass = O.cusp ∧
    O.rank_one_quotient.quotientEquiv
        O.rank_one_quotient.distinguishedClass = 1 ∧
    O.rank_one_quotient.distinguishedClass ≠ 0

/-- The cusp slot statement is exactly the supplied boundary-origin
record: the distinguished nonzero quotient class generates the rank-one
quotient and maps to the cusp. -/
theorem arithmeticCuspOriginCompatibility_of_supply
    {X : Iut.HyperbolicOrbicurve A.K}
    (O : TorsionQuotientBoundaryOrigin l A X) :
    ArithmeticCuspOriginCompatibility O :=
  ⟨O.originMap_nonzeroClass_spec, O.distinguishedClass_is_generator,
    O.distinguishedClass_nonzero⟩

/-! ## Integration note: the D9 compatibility supply

The consumer structure `D9CompatibilitySupply` and the bundle
`D4D9Supply` live in `SourceDefinition31D4D9Supply.lean` (owner: the
D3-D11 line).  Instantiate its five slots there with the four concrete
statements above:

* `reduction := ArithmeticReductionCompatibility P C Q`, proved by
  `arithmeticReductionCompatibility_of_supply`;
* `torsion := ArithmeticTorsionCompatibility T`, proved by
  `arithmeticTorsionCompatibility_of_clause`;
* `sections := ArithmeticSectionCompatibility P`, proved by
  `arithmeticSectionCompatibility_canonical`;
* `cusp := ArithmeticCuspOriginCompatibility O`, proved by
  `arithmeticCuspOriginCompatibility_of_supply`;
* `orbicurve` stays the supplied proposition (parked card).

This module deliberately does not import the bundle module: the wiring
is a consumer-side edit recorded in the report (integration request
block, `logs/coordination/estimates-rec8-h1-review-20261016.md`).
-/

end InitialThetaSource

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Parked card: the orbicurve slot of the D9 five arithmetic
compatibilities. -/
def sourceDefinition31D9OrbicurveSlotGap : Obligation :=
  { id := "IUT-I.definition-3.1-D9-orbicurve-slot"
    source :=
      "IUT I, Definition 3.1(d) (extraction lines 3185-3215)"
    status := VerificationStatus.pending
    note :=
      "PARK. Object: the actual K-core orbicurve C_K := C_F x_F K of " ++
        "type (1,l-tors)^pm over K with certified etale fundamental " ++
        "groups, together with the K-core identification of " ++
        "Definition 3.1(d). Quantifier: for every " ++
        "A : InitialThetaArithmeticData l, with no further hypotheses " ++
        "(the paper's (d) is a source existence claim on C_K). " ++
        "Conclusion: a compiled concrete orbicurve clause with the " ++
        "K-core identification, yielding a concrete content for the " ++
        "D9 orbicurve slot (D9CompatibilitySupply.orbicurve) and the " ++
        "D6 gate body. Why not derivable from the current tree: " ++
        "(i) no supplier constructs an orbicurve over A.K from A " ++
        "alone; the compiled constructors " ++
        "(SourceClauseConstructors.ofFundamentalGroup, " ++
        "exactSequenceOfFundamentalGroup) take an actual orbicurve with " ++
        "certified pi_1 as input, and the sign-quotient chain " ++
        "(SourceCompletion.lean:66, cK : Iut.HyperbolicOrbicurve A.K) " ++
        "likewise takes the object as a field; (ii) the foundation " ++
        "Iut.Foundations.Orbicurve provides the structures " ++
        "(EtaleStackOverField, HyperbolicOrbicurve, " ++
        "OrbicurveBoundaryCusp) but no base-change construction of the " ++
        "K-core from A.curve; (iii) a signature-only surrogate " ++
        "(OrbicurveSignature of type (1,l-tors)^pm) was rejected: it " ++
        "would replace the object by metadata and weaken the slot. " ++
        "Consumers: d6_status, D9 orbicurve slot, d11EntryData " ++
        "orbCompat parameter. Owner route: Helmholtz (D3-D11)."
    dependsOn :=
      [ "IUT-I.definition-3.1-D6",
        "IUT-I.definition-3.1-D9" ] }

/-- Parked card: the local generator half of the cusp slot. -/
def sourceDefinition31D9CuspLocalGeneratorGap : Obligation :=
  { id := "IUT-I.definition-3.1-D9-cusp-local-generator"
    source :=
      "IUT I, Definition 3.1(f), second half (extraction lines 3276-3295)"
    status := VerificationStatus.pending
    note :=
      "PARK. Object: for v in V^bad, the local models X_v-dot, " ++
        "C_v-dot over K_v of type (1,(Z/lZ)^Theta), (1,(Z/lZ)^Theta)^pm " ++
        "(obtained by extracting an l-th root of the theta function), " ++
        "the open subgroups Pi_{X_v-dot} subset Pi_{C_v-dot} subset " ++
        "Pi_{C_v}, and the statement that the local cusp epsilon_v is " ++
        "the cusp arising from the canonical generator +-1 of the " ++
        "local quotient Z-hat. Quantifier: for every v in V^bad " ++
        "(per bad place), for every A. Assumptions: the local type " ++
        "(1,Z/lZ)^pm condition is itself a source condition of (e). " ++
        "Conclusion: existence of the local models and the +-1-cusp " ++
        "identification. Why not derivable: the [EtTh] section-2 local " ++
        "theory (theta extraction, root models) is not formalized " ++
        "anywhere in the tree; OrbicurveBoundaryCusp exists as a " ++
        "structure but there is no local (Z/lZ)-quotient carrier and " ++
        "no canonical-generator cusp; the compiled cusp-origin content " ++
        "(TorsionQuotientBoundaryOrigin, distinguished class of the " ++
        "rank-one quotient, arithmeticCuspOriginCompatibility_of_supply) " ++
        "is the global K-side algebraic quotient, not the bad-place " ++
        "local generator condition. Consumers: D8 cusp slot residual, " ++
        "D9 cusp slot residual. Owner route: Helmholtz (D3-D11)."
    dependsOn :=
      [ "IUT-I.definition-3.1-D8",
        "IUT-I.definition-3.1-D9" ] }

end LeanFormal.IUT.Audit
