# S2134: D9 effective descent — exact first missing, amalgamation form, base case proved

Date: 2026-11-02. Status: the effective-descent half of the D9 stack target is isolated
exactly and partially proved (base case / maximal sieve). No IsStack instance is
produced, no effective-descent statement is assumed, no sorry, no new axiom.

## Layer

D9 stack field (Route B, large Cat.{u+1,u+1} target), specifically the second field
S2093SheafEffectiveDescent of S2093's exact decomposition IsStack <-> prestack /effective descent. Not the C_F quotient witness, not the K-side cover, not Cor. 3.12.

## Source objects

- F = S2029SheafPrestack K = (Iut.SchemeOverField.etaleTopology K).pseudofunctorOver (Type u),
  S2029GiraudStackificationActual.
- S2093SheafEffectiveDescent K (S2093D9StackActual): forall U (R : Sieve U),
  R in etaleTopology -> EssSurj of F.toDescentData on the family of all arrows of R.
- S2093EtalePrecoverage K (S2093): the etale precoverage on SchemeOverField K, with
  toGrothendieck = etaleTopology (S2093EtalePrecoverage_toGrothendieck).
- S2103FirstMissing K (S2103D9PrestackActual): the prestack-half naturality input.
- Mathlib v4.32.2 DescentData / IsPrestack / IsStack / Precoverage; no IsStack instance.

## Domain

X : SchemeOverField K; R : Presieve X; actual precoverage covers
(S2093EtalePrecoverage K).coverings X; descent data D : F.DescentData (fun g : R.category => g.obj.hom).

## BUILT

File: tmp/sheaf/xif/paper/S2134D9DescentActual.lean (404 lines, EXIT=0)

Section 1 (general pseudofunctor F : LocallyDiscrete Cᵒᵖ ⤳ Cat):
- HasEffectiveDescent F f := (F.toDescentData f).EssSurj.
- HasEffectiveDescentPresieve F R := EssSurj for the family of all arrows of R.
- hasEffectiveDescent_iff_of_sieve_eq: two families generating the same sieve have
  equivalent effective descent (uses Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq
  plus EssSurj transfer along a fully faithful equivalence).
- hasEffectiveDescentPresieve_iff_of_generate_eq: presieve form of the same.
- Amalgam F f D: structure with M : F.obj S and iso : (F.toDescentData f).obj M ≅ D.
- hasEffectiveDescent_iff_amalgam: effective descent <-> every descent datum has an
  amalgamation.

Section 2 (base case, arbitrary F):
- idFamilyDescentIso: for the family (𝟙 S) indexed by Unit, every descent datum D is
  isomorphic to the descent data of D.obj () — the comparison is the pseudofunctor unit
  F.mapId. (No axioms at all.)
- hasEffectiveDescent_idFamily: effective descent for the identity cover.
- sieve_ofArrows_idFamily: the identity family generates ⊤.
- hasEffectiveDescentPresieve_of_generate_top: effective descent for EVERY presieve R with
  Sieve.generate R = ⊤ (covers refined by the identity).
- hasEffectiveDescentPresieve_of_contains_isSplitEpi: every cover containing a split
  epimorphism (e.g. an isomorphism) has effective descent.
- hasEffectiveDescentPresieve_top: effective descent for the maximal presieve.

Section 3 (D9 site):
- S2134EffDescentOnEtaleFamilies K: effective descent for every actual precoverage cover.
- S2134EffDescentOnEtaleFamilies_iff_amalgam: the same as amalgamations for all descent
  data on all actual etale covers.
- S2134FirstMissing K := S2134EffDescentOnEtaleFamilies K (the named exact first missing;
  no inhabitant asserted).
- S2134EffDescentOnEtaleFamilies_iff_proper: only covers with proper generated sieve matter.
- S2134EffDescent_identityCover: Presieve.singleton (𝟙 S) is an actual precoverage cover
  (HasIsos) AND has effective descent.
- S2134EffDescent_of_contains_isSplitEpi: unconditional effective descent for any cover
  containing a split epi.
- S2093SheafEffectiveDescent_iff_presieve_form: the sieve-level target is equivalent to
  the presieve-level form forall R, Sieve.generate R in J.
- S2093SheafEffectiveDescent_iff_proper_presieves: the target is equivalent to its
  restriction to proper generated sieves (the ⊤ case is automatic).
- S2134EffDescentOnEtaleFamilies_of_effectiveDescent: target -> family form.
- S2134FirstMissing_of_stackMissing: D9 stack missing -> S2134FirstMissing.
- S2093SheafEffectiveDescent_of_prestack_and_families: prestack half + family form ->
  full effective-descent half (via IsStack.of_precoverage on the precoverage).
- S2093LargeSheafStackMissing_iff_halves: the D9 stack target is exactly
  S2093SheafPrestack / S2134EffDescentOnEtaleFamilies.
- S2093SheafStackOnEtaleFamilies_iff_halves: the same for S2093's family-level target.
- S2093LargeSheafStackMissing_of_naturality_and_families: S2103FirstMissing +
  S2134EffDescentOnEtaleFamilies -> D9 stack target.

## PROVED

- All of the above are unconditional theorems (no hypothesis of the form
  "effective descent" or "IsStack" is assumed); the conditional assembly theorems take
  their inputs explicitly as arguments and do not assert them.
- The base case shows that effective descent is effective for all covers refined by the
  identity, in particular for the maximal sieve, for the identity cover and for every
  cover containing a split epimorphism; on the D9 site this includes an actual
  precoverage cover (the identity cover).
- Exact decomposition: the D9 stack target = prestack half (S2100/S2103) + effective
  descent on actual etale covering families (S2134FirstMissing).

## MISSING exact

S2134FirstMissing K: effective descent for an arbitrary (proper) actual etale covering
family, equivalently (section 1) the construction of an amalgamation for an arbitrary
descent datum on such a cover. No such construction exists in Mathlib v4.32.2: there is
no instance of Pseudofunctor.IsStack at all in the library (only the class, its
projection lemmas and the constructors IsStack.of_isStackFor / IsStack.of_precoverage,
which take the stack condition as a hypothesis), and in particular no "sheaves on
slices form a stack" theorem / Cech descent comparison for the slice topos.

The base case does NOT apply to a general etale cover: it reads the glued object off the
index of the identity (or of a split epimorphism) and therefore needs a split cover.
This is the precise sense in which the obstruction is the non-split nature of a general
etale cover.

## No fake

No IsStack instance is produced. No pointwise-only, label-only, Shrink/ULift or
representable substitution is used. The only axioms are propext, Classical.choice,
Quot.sound (checked with #print axioms on every declaration listed in section 4 of the
file; no sorryAx).

## Consumer

S2134FirstMissing + S2103FirstMissing -> S2093LargeSheafStackMissing ->
S2093LargeCFDataExact -> S1964QuotientStructure (D9 slot).

## Verification

- Lean file: tmp/sheaf/xif/paper/S2134D9DescentActual.lean
- EXIT=0 (lake env lean -j1 -R D:/lean -o ...S2134D9DescentActual.olean ...)
- SHA256 (lean): 12C9CAF9CE98B2E0584C689B1B1880B14B159A7A92C939C7FF1DC7AB4ECC4301
- olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2134D9DescentActual.olean
- olean size 476224; SHA256 (olean): D15BE63E039524789876E0FE57ABC1706CCDEBC82F2B1B7567F630D7610C97A9
- axioms: propext, Classical.choice, Quot.sound (no sorryAx, no new axiom)
- statement_compiles=true; proof_body_checked=true (all declarations); kernel_closed=true
  (for the listed theorems); target_accepted=false (S2134FirstMissing has no inhabitant).

## Reports / files read

- tmp/sheaf/xif/paper/S2093D9StackActual.lean
- tmp/sheaf/xif/paper/S2103D9PrestackActual.lean
- tmp/sheaf/xif/paper/S2029GiraudStackificationActual.lean, S2050D9UniverseChoiceActual.lean,
  S2100D9PrestackNaturalityActual.lean
- Mathlib: CategoryTheory/Sites/Descent/{DescentData,IsPrestack,IsStack,Precoverage}.lean,
  CategoryTheory/Sites/{Sieves,Over,PseudofunctorSheafOver,PrecoverageToGrothendieck}.lean,
  CategoryTheory/EssentialImage.lean, CategoryTheory/Equivalence.lean
- coord/reports/S2043-d9-full.md, S2050-d9-universe.md, S2100-d9-prestack.md

(S2093SheafEffectiveDescent is a declaration in S2093D9StackActual.lean, not a file.)
