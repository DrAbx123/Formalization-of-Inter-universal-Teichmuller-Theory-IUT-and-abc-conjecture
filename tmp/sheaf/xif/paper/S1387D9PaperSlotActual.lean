import tmp.sheaf.xif.paper.S1319OrbicurveClauseActual
import tmp.sheaf.xif.paper.S1360D9OrbicurveSlotActual
import tmp.sheaf.xif.paper.S1376PaperKCoreRestatementActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31OrbicurveInstance

/-!
# S1387: the paper D9 orbicurve slot, or its exact first field

S1360 records the paper D9 slot `S1360D9OrbicurveSlot l` as a paper
(1, l-tors) orbicurve slot together with the K-core identification of
Definition 3.1(d).  S1376 restates the K-core at the actual C_K and gives the
conditional constructor `S1376PaperClauseD.toD9Slot`, which takes exactly a
paper clause (d) record and the nonterminality certificate `S.xK`.

The remaining D9 content is therefore precisely:

* an actual hyperbolic orbicurve `X` over `K = (S1280Arithmetic l).K` with
  signature `(1, l-tors)`;
* a nonterminality certificate for `X` (not a point fiber, not the terminal
  constant stack);
* the certified orbifold fundamental-group data of `X` over `G_K`;
* the K-core identification `X -> C_K`.

This file separates those fields exactly.  The non-group first field is
`S1387D9FirstField l`; the residual group field is `S1387D9Remainder`; the
full slot is proved equivalent to a sigma type over them plus the K-core
(`S1387D9SlotEquiv`).  Hence the full D9 slot is nonempty exactly when a first
field, its group data and a K-core identification exist
(`S1387D9Slot_nonempty_iff`).

The first field is constructed from actual data only:

* from a non-point etale stack fiber with effective descent
  (`S1387D9FirstFieldOfFiber`), so no terminal and no point fiber;
* from the exact missing D6 geometric realization of Example36
  (`S1387D9FirstFieldOfMissingD6`);
* from a paper clause (d) of S1376 plus nonterminality
  (`S1387D9FirstFieldOfPaperClause`), with first field definitionally `S.xK`;
* from the S1348 D6 exact first field together with exactly the D9 extra
  fields (`S1387D9FirstFieldOfS1348`).

Conversely every D9 slot gives the S1348 D6 first field by forgetting the
signature/nonterminal/K-core data (`S1387S1348FirstFieldOfD9`), so the D9
first field is a genuine refinement of the S1348 exact first field rather than
a replacement for it.

## Exact boundary

The tree contains no inhabitant of `MissingD6GeometricRealization K`
(Example36 proves that the point and terminal fibers fail it and records that
no actual non-point etale stack fiber is constructed) and no inhabitant of
`OrbicurveEtaleFundamentalGroup` for any orbicurve.  Therefore this file does
not assert `Nonempty (S1360D9OrbicurveSlot l)`.  It characterizes that slot
exactly and constructs it from the exact first field plus group and K-core
data.  No terminal stack, point fiber, l-torsion sequence, arbitrary carrier,
new assumption or placeholder proof is used as a substitute.

This file does not modify or depend on the D6 orbifold-Pi first-field file of
S1359/S1382; it reuses only the S1319 nonterminal predicate and the Example36
D6 realization interface.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1387D9PaperSlotActual

universe u

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1360D9OrbicurveSlotActual
open LeanFormal.IUT.XiFPaper.S1376PaperKCoreRestatementActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

/-- The S1280 K-side field over which the D9 orbicurve lives. -/
abbrev S1387K (l : PrimeGeFive) : Type := (S1280Arithmetic l).K

/-- The absolute Galois group used by the D9 orbifold Pi data. -/
abbrev S1387Galois (l : PrimeGeFive) : ProfiniteGrp :=
  Iut.AbsoluteGaloisProfinite (S1387K l)

/-- The exact non-group first field of the paper D9 slot: an actual hyperbolic
orbicurve over `K`, nonterminal, with signature `(1, l-tors)`.

This is the first field `X` of `S1360D9OrbicurveSlot` together with the two
certificates carried by `S1360PaperOrbicurveSlotAtK` other than the group
data. -/
structure S1387D9FirstField (l : PrimeGeFive) where
  /-- The actual K-side hyperbolic orbicurve. -/
  X : Iut.HyperbolicOrbicurve (S1387K l)
  /-- `X` is not a point fiber. -/
  nonterminal : S1319NonterminalFiber X
  /-- The paper K-side signature. -/
  signature : X.signature = sourceTypeOneLTorsion l

/-- The exact residual field after the first field: the certified arithmetic
and geometric orbifold fundamental-group data over the absolute Galois group
of `K`. -/
abbrev S1387D9Remainder (l : PrimeGeFive) (F : S1387D9FirstField l) : Type 1 :=
  Iut.OrbicurveFundamentalGroupData F.X (S1387Galois l)

/-- The stack content of the first field: a non-point etale stack fiber with
effective descent for the big etale topology over `K`. -/
structure S1387D9StackFirstField (l : PrimeGeFive) where
  fiber : Iut.EtaleStackPseudofunctor (S1387K l)
  isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology (S1387K l))
  nonPoint : ¬ IsPointFiber fiber

/-! ## 1. The first field from an actual non-point stack fiber -/

/-- Insert the paper `(1, l-tors)` signature into an actual non-point etale
stack fiber.  The nonterminality proof is exactly non-pointness of the fiber;
the signature certificate is the hyperbolic `(1, l-tors)` signature. -/
noncomputable def S1387D9FirstFieldOfFiber (l : PrimeGeFive)
    (fiber : Iut.EtaleStackPseudofunctor (S1387K l))
    (isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology (S1387K l)))
    (h : ¬ IsPointFiber fiber) : S1387D9FirstField l := by
  classical
  refine
    { X := realizedHyperbolicOrbicurve (S1387K l) fiber isStack
        (sourceTypeOneLTorsion l) (sourceTypeOneLTorsion_hyperbolic l)
      nonterminal := ?_
      signature := rfl }
  change ∃ U : (Iut.SchemeOverField (S1387K l))ᵒᵖ,
    ¬ Subsingleton (fiber.obj (LocallyDiscrete.mk U))
  by_contra h'
  apply h
  intro U
  by_contra hU
  exact h' ⟨U, hU⟩

@[simp] theorem S1387D9FirstFieldOfFiber_X (l : PrimeGeFive)
    (fiber : Iut.EtaleStackPseudofunctor (S1387K l))
    (isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology (S1387K l)))
    (h : ¬ IsPointFiber fiber) :
    (S1387D9FirstFieldOfFiber l fiber isStack h).X.stack.fiber = fiber := rfl

@[simp] theorem S1387D9FirstFieldOfFiber_signature (l : PrimeGeFive)
    (fiber : Iut.EtaleStackPseudofunctor (S1387K l))
    (isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology (S1387K l)))
    (h : ¬ IsPointFiber fiber) :
    (S1387D9FirstFieldOfFiber l fiber isStack h).X.signature =
      sourceTypeOneLTorsion l := rfl

/-- The stack content of a first field. -/
noncomputable def S1387D9StackFirstFieldOfFirstField (l : PrimeGeFive)
    (F : S1387D9FirstField l) : S1387D9StackFirstField l where
  fiber := F.X.stack.fiber
  isStack := F.X.stack.isStack
  nonPoint := (s1360Nonterminal_iff_not_pointFiber F.X).mp F.nonterminal

/-- The first field reconstructed from its exact stack content. -/
noncomputable def S1387D9FirstFieldOfStackFirstField (l : PrimeGeFive)
    (S : S1387D9StackFirstField l) : S1387D9FirstField l :=
  S1387D9FirstFieldOfFiber l S.fiber S.isStack S.nonPoint

/-- The first field is nonempty exactly when a non-point etale stack fiber
over `K` exists.  This is the precise stack content of the first field. -/
theorem S1387D9FirstField_nonempty_iff_stackFirstField (l : PrimeGeFive) :
    Nonempty (S1387D9FirstField l) ↔
      Nonempty (S1387D9StackFirstField l) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨S1387D9StackFirstFieldOfFirstField l F⟩
  · rintro ⟨S⟩
    exact ⟨S1387D9FirstFieldOfStackFirstField l S⟩

/-- The exact missing D6 geometric realization of Example36 supplies the
first field: the fiber is the supplied one, its signature is the paper
`(1, l-tors)` signature, and nonterminality is the D6 nondegeneracy. -/
noncomputable def S1387D9FirstFieldOfMissingD6 (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1387K l)) :
    S1387D9FirstField l :=
  S1387D9FirstFieldOfFiber l D.fiber D.isStack D.nondegenerate

@[simp] theorem S1387D9FirstFieldOfMissingD6_fiber (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1387K l)) :
    (S1387D9FirstFieldOfMissingD6 l D).X.stack.fiber = D.fiber := rfl

@[simp] theorem S1387D9FirstFieldOfMissingD6_signature (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1387K l)) :
    (S1387D9FirstFieldOfMissingD6 l D).X.signature =
      sourceTypeOneLTorsion l := rfl

theorem S1387D9FirstFieldOfMissingD6_nonterminal (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1387K l)) :
    S1319NonterminalFiber (S1387D9FirstFieldOfMissingD6 l D).X :=
  (S1387D9FirstFieldOfMissingD6 l D).nonterminal

/-! ## 2. The first field from the S1376 paper clause (d) -/

/-- The first field of a paper clause (d) plus its nonterminality certificate:
the actual `S.xK`, with the S1376 K-core signature. -/
noncomputable def S1387D9FirstFieldOfPaperClause
    {l : PrimeGeFive}
    {S : SourceSignQuotientData (S1280Arithmetic l)}
    {C : SourceClauseA (S1280Arithmetic l) S}
    {B : SourceClauseB (S1280Arithmetic l) S C}
    {D : SourceClauseC (S1280Arithmetic l) S C B}
    (P : S1376PaperClauseD S C B D)
    (h : S1319NonterminalFiber S.xK) : S1387D9FirstField l where
  X := S.xK
  nonterminal := h
  signature := P.xK_type

@[simp] theorem S1387D9FirstFieldOfPaperClause_X
    {l : PrimeGeFive}
    {S : SourceSignQuotientData (S1280Arithmetic l)}
    {C : SourceClauseA (S1280Arithmetic l) S}
    {B : SourceClauseB (S1280Arithmetic l) S C}
    {D : SourceClauseC (S1280Arithmetic l) S C B}
    (P : S1376PaperClauseD S C B D)
    (h : S1319NonterminalFiber S.xK) :
    (S1387D9FirstFieldOfPaperClause P h).X = S.xK := rfl

@[simp] theorem S1387D9FirstFieldOfPaperClause_signature
    {l : PrimeGeFive}
    {S : SourceSignQuotientData (S1280Arithmetic l)}
    {C : SourceClauseA (S1280Arithmetic l) S}
    {B : SourceClauseB (S1280Arithmetic l) S C}
    {D : SourceClauseC (S1280Arithmetic l) S C B}
    (P : S1376PaperClauseD S C B D)
    (h : S1319NonterminalFiber S.xK) :
    (S1387D9FirstFieldOfPaperClause P h).X.signature =
      sourceTypeOneLTorsion l :=
  (S1387D9FirstFieldOfPaperClause P h).signature

/-- Any paper clause (d) with nonterminality gives the full D9 slot; this is
the S1376 constructor, re-exposed at the exact first field. -/
noncomputable def S1387D9SlotOfPaperClause
    {l : PrimeGeFive}
    {S : SourceSignQuotientData (S1280Arithmetic l)}
    {C : SourceClauseA (S1280Arithmetic l) S}
    {B : SourceClauseB (S1280Arithmetic l) S C}
    {D : SourceClauseC (S1280Arithmetic l) S C B}
    (P : S1376PaperClauseD S C B D)
    (h : S1319NonterminalFiber S.xK) :
    S1360D9OrbicurveSlot l :=
  P.toD9Slot h

@[simp] theorem S1387D9SlotOfPaperClause_firstField
    {l : PrimeGeFive}
    {S : SourceSignQuotientData (S1280Arithmetic l)}
    {C : SourceClauseA (S1280Arithmetic l) S}
    {B : SourceClauseB (S1280Arithmetic l) S C}
    {D : SourceClauseC (S1280Arithmetic l) S C B}
    (P : S1376PaperClauseD S C B D)
    (h : S1319NonterminalFiber S.xK) :
    (S1387D9SlotOfPaperClause P h).firstField = S.xK := rfl

@[simp] theorem S1387D9SlotOfPaperClause_kCore
    {l : PrimeGeFive}
    {S : SourceSignQuotientData (S1280Arithmetic l)}
    {C : SourceClauseA (S1280Arithmetic l) S}
    {B : SourceClauseB (S1280Arithmetic l) S C}
    {D : SourceClauseC (S1280Arithmetic l) S C B}
    (P : S1376PaperClauseD S C B D)
    (h : S1319NonterminalFiber S.xK) :
    (S1387D9SlotOfPaperClause P h).kCore = P.kCore := rfl

theorem S1387D9SlotOfPaperClause_signature
    {l : PrimeGeFive}
    {S : SourceSignQuotientData (S1280Arithmetic l)}
    {C : SourceClauseA (S1280Arithmetic l) S}
    {B : SourceClauseB (S1280Arithmetic l) S C}
    {D : SourceClauseC (S1280Arithmetic l) S C B}
    (P : S1376PaperClauseD S C B D)
    (h : S1319NonterminalFiber S.xK) :
    (S1387D9SlotOfPaperClause P h).firstField.signature =
      sourceTypeOneLTorsion l :=
  (S1387D9SlotOfPaperClause P h).signature

/-! ## 3. Exact decomposition of the paper D9 slot -/

/-- A first field together with its group data is exactly the S1360 paper
orbicurve slot. -/
noncomputable def S1387PaperSlotOfSigma (l : PrimeGeFive)
    (P : Sigma fun F : S1387D9FirstField l => S1387D9Remainder l F) :
    S1360PaperOrbicurveSlotAtK l where
  X := P.1.X
  nonterminal := P.1.nonterminal
  signature := P.1.signature
  groups := P.2

/-- The S1360 paper orbicurve slot, split into first field and group data. -/
noncomputable def S1387SigmaOfPaperSlot (l : PrimeGeFive)
    (S : S1360PaperOrbicurveSlotAtK l) :
    Sigma fun F : S1387D9FirstField l => S1387D9Remainder l F :=
  ⟨⟨S.X, S.nonterminal, S.signature⟩, S.groups⟩

/-- The paper orbicurve slot is exactly a first field together with the
residual orbifold fundamental-group data. -/
noncomputable def S1387PaperSlotEquiv (l : PrimeGeFive) :
    S1360PaperOrbicurveSlotAtK l ≃
      (Sigma fun F : S1387D9FirstField l => S1387D9Remainder l F) where
  toFun := S1387SigmaOfPaperSlot l
  invFun := S1387PaperSlotOfSigma l
  left_inv S := by
    cases S
    rfl
  right_inv P := by
    rcases P with ⟨⟨X, nonterminal, signature⟩, groups⟩
    rfl

/-- The first field of a paper orbicurve slot. -/
noncomputable def S1387D9FirstFieldOfPaperSlot (l : PrimeGeFive)
    (S : S1360PaperOrbicurveSlotAtK l) : S1387D9FirstField l :=
  (S1387SigmaOfPaperSlot l S).1

@[simp] theorem S1387D9FirstFieldOfPaperSlot_X (l : PrimeGeFive)
    (S : S1360PaperOrbicurveSlotAtK l) :
    (S1387D9FirstFieldOfPaperSlot l S).X = S.X := rfl

/-- Build the full D9 slot from the exact first field, its group data and the
K-core identification.  The first field signature is definitionally the
`x_type` required by the K-core. -/
noncomputable def S1387D9SlotOf (l : PrimeGeFive)
    (F : S1387D9FirstField l)
    (groups : S1387D9Remainder l F)
    (kCore : S1360KCoreIdentification l F.X) :
    S1360D9OrbicurveSlot l where
  orbicurve :=
    { X := F.X
      nonterminal := F.nonterminal
      signature := F.signature
      groups := groups }
  kCore := kCore

@[simp] theorem S1387D9SlotOf_firstField (l : PrimeGeFive)
    (F : S1387D9FirstField l)
    (groups : S1387D9Remainder l F)
    (kCore : S1360KCoreIdentification l F.X) :
    (S1387D9SlotOf l F groups kCore).firstField = F.X := rfl

@[simp] theorem S1387D9SlotOf_kCore (l : PrimeGeFive)
    (F : S1387D9FirstField l)
    (groups : S1387D9Remainder l F)
    (kCore : S1360KCoreIdentification l F.X) :
    (S1387D9SlotOf l F groups kCore).kCore = kCore := rfl

@[simp] theorem S1387D9SlotOf_groups (l : PrimeGeFive)
    (F : S1387D9FirstField l)
    (groups : S1387D9Remainder l F)
    (kCore : S1360KCoreIdentification l F.X) :
    (S1387D9SlotOf l F groups kCore).orbicurve.groups = groups := rfl

/-- The full paper D9 slot from the exact missing D6 geometric realization,
its certified orbifold fundamental-group data, and the K-core
identification.  The first field is the realization's non-point fiber with
the paper signature; no terminal or point fiber is used. -/
noncomputable def S1387D9SlotOfMissingD6 (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1387K l))
    (groups : S1387D9Remainder l (S1387D9FirstFieldOfMissingD6 l D))
    (kCore :
      S1360KCoreIdentification l (S1387D9FirstFieldOfMissingD6 l D).X) :
    S1360D9OrbicurveSlot l :=
  S1387D9SlotOf l (S1387D9FirstFieldOfMissingD6 l D) groups kCore

@[simp] theorem S1387D9SlotOfMissingD6_firstField_fiber (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1387K l))
    (groups : S1387D9Remainder l (S1387D9FirstFieldOfMissingD6 l D))
    (kCore :
      S1360KCoreIdentification l (S1387D9FirstFieldOfMissingD6 l D).X) :
    (S1387D9SlotOfMissingD6 l D groups kCore).firstField.stack.fiber =
      D.fiber := rfl

@[simp] theorem S1387D9SlotOfMissingD6_signature (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1387K l))
    (groups : S1387D9Remainder l (S1387D9FirstFieldOfMissingD6 l D))
    (kCore :
      S1360KCoreIdentification l (S1387D9FirstFieldOfMissingD6 l D).X) :
    (S1387D9SlotOfMissingD6 l D groups kCore).firstField.signature =
      sourceTypeOneLTorsion l :=
  (S1387D9SlotOfMissingD6 l D groups kCore).signature

/-- Consequently a D6 geometric realization plus the two exact residual
fields gives an inhabitant of the paper D9 slot. -/
theorem S1387D9Slot_nonempty_of_missingD6 (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1387K l))
    (groups : S1387D9Remainder l (S1387D9FirstFieldOfMissingD6 l D))
    (kCore :
      S1360KCoreIdentification l (S1387D9FirstFieldOfMissingD6 l D).X) :
    Nonempty (S1360D9OrbicurveSlot l) :=
  ⟨S1387D9SlotOfMissingD6 l D groups kCore⟩

/-- The full D9 slot is exactly a first field, its group data and a K-core
identification. -/
noncomputable def S1387D9SlotEquiv (l : PrimeGeFive) :
    S1360D9OrbicurveSlot l ≃
      (Sigma fun F : S1387D9FirstField l =>
        S1387D9Remainder l F × S1360KCoreIdentification l F.X) where
  toFun S :=
    ⟨⟨S.orbicurve.X, S.orbicurve.nonterminal, S.orbicurve.signature⟩,
      S.orbicurve.groups, S.kCore⟩
  invFun P :=
    { orbicurve :=
        { X := P.1.X
          nonterminal := P.1.nonterminal
          signature := P.1.signature
          groups := P.2.1 }
      kCore := P.2.2 }
  left_inv S := by
    cases S
    rfl
  right_inv P := by
    rcases P with ⟨⟨X, nonterminal, signature⟩, groups, kCore⟩
    rfl

/-- The exact nonemptiness characterization of the paper D9 slot. -/
theorem S1387D9Slot_nonempty_iff (l : PrimeGeFive) :
    Nonempty (S1360D9OrbicurveSlot l) ↔
      ∃ F : S1387D9FirstField l,
        Nonempty (S1387D9Remainder l F) ∧
          Nonempty (S1360KCoreIdentification l F.X) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨⟨S.orbicurve.X, S.orbicurve.nonterminal, S.orbicurve.signature⟩,
      ⟨S.orbicurve.groups⟩, ⟨S.kCore⟩⟩
  · rintro ⟨F, ⟨groups⟩, ⟨kCore⟩⟩
    exact ⟨S1387D9SlotOf l F groups kCore⟩

/-- The first field of a D9 slot. -/
noncomputable def S1387D9FirstFieldOfSlot (l : PrimeGeFive)
    (S : S1360D9OrbicurveSlot l) : S1387D9FirstField l :=
  ⟨S.orbicurve.X, S.orbicurve.nonterminal, S.orbicurve.signature⟩

@[simp] theorem S1387D9FirstFieldOfSlot_X (l : PrimeGeFive)
    (S : S1360D9OrbicurveSlot l) :
    (S1387D9FirstFieldOfSlot l S).X = S.orbicurve.X := rfl

/-! ## 4. Relation to the S1348 D6 exact first field -/

/-- The S1348 D6 exact first field, with exactly the D9 signature and
nonterminality certificates, gives the D9 first field.  No datum is dropped:
the group component of the S1348 field is kept separately below. -/
noncomputable def S1387D9FirstFieldOfS1348 (l : PrimeGeFive)
    (F : S1348D6FirstMissingField l)
    (h : S1319NonterminalFiber F.1)
    (hs : F.1.signature = sourceTypeOneLTorsion l) :
    S1387D9FirstField l where
  X := F.1
  nonterminal := h
  signature := hs

@[simp] theorem S1387D9FirstFieldOfS1348_X (l : PrimeGeFive)
    (F : S1348D6FirstMissingField l)
    (h : S1319NonterminalFiber F.1)
    (hs : F.1.signature = sourceTypeOneLTorsion l) :
    (S1387D9FirstFieldOfS1348 l F h hs).X = F.1 := rfl

/-- The group component of the S1348 exact first field is exactly the D9
residual group data at the first field built from it. -/
noncomputable def S1387D9RemainderOfS1348 (l : PrimeGeFive)
    (F : S1348D6FirstMissingField l)
    (h : S1319NonterminalFiber F.1)
    (hs : F.1.signature = sourceTypeOneLTorsion l) :
    S1387D9Remainder l (S1387D9FirstFieldOfS1348 l F h hs) :=
  F.2

/-- The D9 slot from the S1348 exact first field plus exactly the D9 extra
fields (nonterminality, paper signature, K-core). -/
noncomputable def S1387D9SlotOfS1348 (l : PrimeGeFive)
    (F : S1348D6FirstMissingField l)
    (h : S1319NonterminalFiber F.1)
    (hs : F.1.signature = sourceTypeOneLTorsion l)
    (kCore : S1360KCoreIdentification l F.1) :
    S1360D9OrbicurveSlot l :=
  S1387D9SlotOf l (S1387D9FirstFieldOfS1348 l F h hs)
    (S1387D9RemainderOfS1348 l F h hs) kCore

@[simp] theorem S1387D9SlotOfS1348_firstField (l : PrimeGeFive)
    (F : S1348D6FirstMissingField l)
    (h : S1319NonterminalFiber F.1)
    (hs : F.1.signature = sourceTypeOneLTorsion l)
    (kCore : S1360KCoreIdentification l F.1) :
    (S1387D9SlotOfS1348 l F h hs kCore).firstField = F.1 := rfl

/-- Every D9 slot gives the S1348 D6 exact first field by forgetting the
signature, nonterminality and K-core data. -/
noncomputable def S1387S1348FirstFieldOfD9 (l : PrimeGeFive)
    (S : S1360D9OrbicurveSlot l) : S1348D6FirstMissingField l :=
  ⟨S.orbicurve.X, S.orbicurve.groups⟩

@[simp] theorem S1387S1348FirstFieldOfD9_fst (l : PrimeGeFive)
    (S : S1360D9OrbicurveSlot l) :
    (S1387S1348FirstFieldOfD9 l S).1 = S.orbicurve.X := rfl

@[simp] theorem S1387S1348FirstFieldOfD9_snd (l : PrimeGeFive)
    (S : S1360D9OrbicurveSlot l) :
    (S1387S1348FirstFieldOfD9 l S).2 = S.orbicurve.groups := rfl

/-! ## 5. Negative controls: no terminal stack and no point fiber -/

theorem S1387D9FirstField_not_pointFiber (l : PrimeGeFive)
    (F : S1387D9FirstField l) :
    ¬ IsPointFiber F.X.stack.fiber :=
  (s1360Nonterminal_iff_not_pointFiber F.X).mp F.nonterminal

theorem S1387D9FirstField_not_terminal (l : PrimeGeFive)
    (F : S1387D9FirstField l) :
    F.X.stack ≠
      Definition31OrbicurveInstance.terminalConstantEtaleStack (S1387K l) :=
  fun h =>
    Definition31OrbicurveInstance.terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier
      (S1387K l) F.X h

theorem S1387D9FirstField_ne_degeneratePointFiber (l : PrimeGeFive)
    (F : S1387D9FirstField l) :
    F.X ≠ degeneratePointFiberOrbicurve (S1387K l) := by
  intro h
  apply S1387D9FirstField_not_pointFiber l F
  rw [h]
  exact degeneratePointFiberOrbicurve_isPointFiber (S1387K l)

theorem S1387D9FirstField_not_terminal_slot {l : PrimeGeFive}
    (S : S1360D9OrbicurveSlot l) :
    S.firstField.stack ≠
      Definition31OrbicurveInstance.terminalConstantEtaleStack (S1387K l) :=
  fun h =>
    Definition31OrbicurveInstance.terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier
      (S1387K l) S.firstField h

theorem S1387DegeneratePointFiber_not_nonterminal (l : PrimeGeFive) :
    ¬ S1319NonterminalFiber (degeneratePointFiberOrbicurve (S1387K l)) :=
  s1360PointFiber_not_nonterminal
    (degeneratePointFiberOrbicurve_isPointFiber (S1387K l))

theorem S1387NoTerminalCarrier (l : PrimeGeFive) :
    ¬ ∃ X : Iut.HyperbolicOrbicurve (S1387K l),
      X.stack = Definition31OrbicurveInstance.terminalConstantEtaleStack (S1387K l) := by
  rintro ⟨X, h⟩
  exact Definition31OrbicurveInstance.terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier
    (S1387K l) X h

/-! ## 6. Axiom footprint -/

#print axioms S1387D9FirstFieldOfFiber
#print axioms S1387D9FirstField_nonempty_iff_stackFirstField
#print axioms S1387D9FirstFieldOfMissingD6
#print axioms S1387D9FirstFieldOfPaperClause
#print axioms S1387D9SlotOfPaperClause
#print axioms S1387PaperSlotEquiv
#print axioms S1387D9SlotOf
#print axioms S1387D9SlotOfMissingD6
#print axioms S1387D9SlotOfMissingD6_firstField_fiber
#print axioms S1387D9SlotOfMissingD6_signature
#print axioms S1387D9Slot_nonempty_of_missingD6
#print axioms S1387D9SlotEquiv
#print axioms S1387D9Slot_nonempty_iff
#print axioms S1387D9FirstFieldOfS1348
#print axioms S1387D9SlotOfS1348
#print axioms S1387S1348FirstFieldOfD9
#print axioms S1387D9FirstField_not_pointFiber
#print axioms S1387D9FirstField_not_terminal
#print axioms S1387D9FirstField_ne_degeneratePointFiber
#print axioms S1387DegeneratePointFiber_not_nonterminal
#print axioms S1387NoTerminalCarrier

end LeanFormal.IUT.XiFPaper.S1387D9PaperSlotActual

end
