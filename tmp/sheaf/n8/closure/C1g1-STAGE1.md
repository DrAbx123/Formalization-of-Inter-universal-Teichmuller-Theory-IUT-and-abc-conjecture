# C1-g1 stage 1: BottomBase connected/epi and global Frobenioid presentation

## Template fields

- Task ID / group / owner / date: C1-g1 / N8 closure / multiradial / 2026-10-22.
- Goal node / SHEAF stage: C1-g1 GlobalExample36Frobenioid / stage 1 only.
- File: tmp/sheaf/n8/closure/C1g1-STAGE1.md (this file). No Lean file is written
  or compiled; no production file is edited.
- Integration/build owner: C1 owner then C10 integration owner; build not
  applicable to this stage.
- Shared interfaces/conflicts: C0-STAGE1 allowed input; C1 place/completion
  binding; group1 production backend; Iut.Foundations.SourceModelFrobenioid.
  No shared definition changed.
- Continuation: after stage 1 review, production patch for
  Example36SourceModelBackend plus a new IUTIII bridge file; then C1 can consume.
- Acceptance: statement_compiles not applicable (no Lean declaration);
  proof_body not checked; this record freezes exact declarations, migration and
  gaps.

## Goal

Migrate the two group1 statements from the standalone trial
tmp/sheaf/n8/Group1Statement.lean into production:

1. BottomBase is connected and all its arrows are epimorphisms.
2. The global Iut.FrobenioidPresentation at the arithmetic base field
   I.initial.arithmetic.Fmod of an actual OriginalInput, obtained by applying
   Iut.SourceModelFrobenioid.Carrier.frobenioidPresentation to the existing
   number-field model input.

The trial file itself must NOT be imported by production or by C1. It is only
the source of the candidate text; the production declarations must be inserted
at the exact production owners listed below.

## Exact production declarations

### BottomBase data

File: LeanFormal/IUT/IUTII/Frobenioid/Example36SourceModelBackend.lean

- SourceModelBackend.BottomBase : Type u := ULift.{u, 0} Unit (:41)
- SourceModelBackend.bottomPoint : BottomBase := ULift.up () (:44)
- instance SourceModelBackend.bottomBaseCategory : Category.{u, u} BottomBase
  with Hom _ _ := ULift.{u,0} Unit, id/comp constant (:46-53)
- SourceModelBackend.BottomFSM : forall {X Y : BottomBase}, (X ⟶ Y) -> Prop :=
  fun _ => True (:56)
- theorem SourceModelBackend.bottomBase_hom_eq_id {X : BottomBase}
    (f : X ⟶ X) : f = 𝟙 X (:59)

Production currently has NO:

- CategoryTheory.IsConnected BottomBase instance;
- theorem proving Epi f for every arrow f : X ⟶ Y in BottomBase.

### Frobenioid presentation constructor

File: Iut/Foundations/SourceModelFrobenioidPresentation.lean:25

~~~text
def Iut.SourceModelFrobenioid.Carrier.frobenioidPresentation
    {D : Type u} [categoryD : Category.{u} D]
    {IsFSM : forall {X Y : D}, (X ⟶ Y) -> Prop}
    {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}
    [IsConnected D]
    (baseTotallyEpimorphic : forall {X Y : D} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation
~~~

This is the exact endpoint of Frobenioids I, Theorem 5.2(ii), packaged through
Definition 1.3. It does not add source Hodge-theater or prime-strip data.

### Number-field model input

File: LeanFormal/IUT/IUTII/Frobenioid/Example36SourceModelBackend.lean

- SourceModelBackend.globalDivisorMonoidOn : DivisorialMonoidOn BottomBase BottomFSM (:419)
- SourceModelBackend.numberFieldSourceModelInput :
    Iut.SourceModelFrobenioid.Input (globalDivisorMonoidOn (F := F)) (:476)

Both are proved production declarations; no new data needed for the presentation.

### Trial declarations (candidate text only)

File: tmp/sheaf/n8/Group1Statement.lean (65 lines)

- instance SourceModelBackend.bottomBase_isConnected :
    CategoryTheory.IsConnected BottomBase
- theorem SourceModelBackend.bottomBase_arrow_epi
    {X Y : BottomBase} (f : X ⟶ Y) : Epi f
- noncomputable def SourceModelBackend.numberFieldFrobenioidPresentation
    (F : Type u) [Field F] [NumberField F] : Iut.FrobenioidPresentation
- noncomputable def Theorem311Source.sourceOriginalInputFrobenioidPresentation
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput l V) : Iut.FrobenioidPresentation

The trial imports production backend + OriginalInput +
Iut.Foundations.SourceModelFrobenioidPresentation. It is not imported by Project
and must not become a production dependency.

## Exact intended production statements

### P1. Connected instance

Location: Example36SourceModelBackend.lean, immediately after
bottomBase_hom_eq_id (:59), inside namespace SourceModelBackend.

~~~text
instance bottomBase_isConnected :
    CategoryTheory.IsConnected (SourceModelBackend.BottomBase) := by
  haveI : Nonempty BottomBase := ⟨bottomPoint⟩
  haveI : Subsingleton BottomBase := inferInstance
  exact CategoryTheory.isConnected_of_nonempty_and_subsingleton
~~~

No new import is needed if the existing import of
Iut.Foundations.SourceModelFrobenioid already provides the IsConnected API;
otherwise the minimal additional import is Mathlib.CategoryTheory.Connected.

### P2. All arrows epi

Location: same file, immediately after P1.

~~~text
theorem bottomBase_arrow_epi
    {X Y : SourceModelBackend.BottomBase} (f : X ⟶ Y) : Epi f := by
  obtain rfl : X = Y := Subsingleton.elim X Y
  rw [bottomBase_hom_eq_id f]
  infer_instance
~~~

Proof: BottomBase is a subsingleton (ULift Unit), hence X = Y; every
endomorphism is the identity by bottomBase_hom_eq_id; identity is epi.

### P3. Number-field Frobenioid presentation

Location: Example36SourceModelBackend.lean, after numberFieldSourceModelInput
(:476) or at the end of the backend section; needs a new import:
Iut.Foundations.SourceModelFrobenioidPresentation.

~~~text
noncomputable def numberFieldFrobenioidPresentation
    (F : Type u) [Field F] [NumberField F] :
    Iut.FrobenioidPresentation :=
  Iut.SourceModelFrobenioid.Carrier.frobenioidPresentation
    (D := BottomBase) (IsFSM := BottomFSM)
    (Phi := globalDivisorMonoidOn (F := F))
    (data := numberFieldSourceModelInput (F := F))
    (fun f => bottomBase_arrow_epi f)
~~~

Note: the implicit [IsConnected BottomBase] is supplied by P1.

### P4. OriginalInput-level global presentation

Do NOT put this in the IUTII backend file: that would make an IUTII file import
IUTIII/OriginalInput and invert the intended layer direction. Put it in a new
production file, for example:

LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInputFrobenioidPresentation.lean

Imports:
- LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
- LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
- Iut.Foundations.SourceModelFrobenioidPresentation (if not already transitively
  available; explicit is safer)

~~~text
namespace LeanFormal.IUT.Theorem311Source
universe ua uv upi umon ui

noncomputable def sourceOriginalInputFrobenioidPresentation
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Iut.FrobenioidPresentation :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend.numberFieldFrobenioidPresentation
    (F := I.initial.arithmetic.Fmod)
~~~

This is the exact C1-facing declaration: it attaches the global Example 3.6(ii)
presentation to the arithmetic base field Fmod of an OriginalInput.

## Allowed input and consumer boundary

Allowed C0 input: l, V, I : OriginalInput l V.

C1-g1 produces only:
- a global Iut.FrobenioidPresentation at Fmod for C1;
- the two base-category facts needed by the constructor.

It does NOT produce:
- a source Hodge theater/prime-strip identification;
- the Example 3.6(iii) natural isomorphism;
- the Prop3.7(iii)-(iv) prime-strip tuple;
- the K2FrobenioidBoundary link;
- an identification between the Frobenioid and OriginalInput's arbitrary V/places.

C1 consumer: C1's actual source-input binding can use
sourceOriginalInputFrobenioidPresentation I as the global Frobenioid of the
arithmetic base field, while keeping V/prime-strip/completion binding as its
separate C1 obligations. C10 later consumes C1; no direct C9/C4/C5 consumer.

The production backend docstring already warns that BottomBase is the model
carrier, not the source base category; C1 must not relabel it as the source
base category.

## Natural-language proof steps

1. Prove Nonempty BottomBase by bottomPoint.
2. Prove Subsingleton BottomBase by ULift Unit.
3. Apply CategoryTheory.isConnected_of_nonempty_and_subsingleton to get
   IsConnected BottomBase.
4. For f : X ⟶ Y, use Subsingleton.elim X Y to reduce to an endomorphism.
5. Rewrite f by bottomBase_hom_eq_id and infer Epi (𝟙 X).
6. Apply frobenioidPresentation with D = BottomBase, IsFSM = BottomFSM,
   Phi = globalDivisorMonoidOn F, data = numberFieldSourceModelInput F, and the
   total-epi proof from step 5.
7. At OriginalInput, instantiate F := I.initial.arithmetic.Fmod and package the
   result as sourceOriginalInputFrobenioidPresentation I.
8. No further source identification is claimed.

All steps are finite category/instance reasoning; no analytic or arithmetic
content is used beyond the existing number-field model input.

## Statement dependencies

- Example36SourceModelBackend.lean: BottomBase (:41), bottomPoint (:44),
  bottomBaseCategory (:46), BottomFSM (:56), bottomBase_hom_eq_id (:59),
  globalDivisorMonoidOn (:419), numberFieldSourceModelInput (:476).
- Iut/Foundations/SourceModelFrobenioidPresentation.lean:25:
  SourceModelFrobenioid.Carrier.frobenioidPresentation.
- SourceOriginalInput.lean: OriginalInput and field initial.arithmetic.Fmod.
- Iut.FrobenioidPresentation type (Iut/Foundations/Frobenioid.lean:915-916).

## Proof dependencies

- CategoryTheory.isConnected_of_nonempty_and_subsingleton (Mathlib).
- Subsingleton.elim; inferInstance for Epi (𝟙 X).
- bottomBase_hom_eq_id (production, proved).
- frobenioidPresentation (production, proved; takes the two base facts as
  hypotheses).
- numberFieldSourceModelInput (production, proved).
No new axiom, no sorry.

## Reusable Mathlib / project donors

- Mathlib: CategoryTheory.IsConnected,
  isConnected_of_nonempty_and_subsingleton, Subsingleton, Epi.
- Project: Example36SourceModelBackend BottomBase/bottomBase_hom_eq_id,
  globalDivisorMonoidOn, numberFieldSourceModelInput;
  Iut.SourceModelFrobenioidPresentation.frobenioidPresentation;
  SourceOriginalInput.OriginalInput and I.initial.arithmetic.Fmod.
- Do not use tmp/sheaf/n8/Group1Statement.lean as an import; use it only as the
  candidate declaration text. It is a discarded standalone trial for production
  purposes.

## Exact gaps

G1. No production IsConnected BottomBase instance yet. P1 is the exact fix.
G2. No production total-epi theorem for BottomBase arrows yet. P2 is the exact
    fix.
G3. No production numberFieldFrobenioidPresentation. P3 is the exact fix; it
    needs the new import of SourceModelFrobenioidPresentation in the IUTII
    backend file.
G4. No production sourceOriginalInputFrobenioidPresentation. P4 is the exact
    fix in a new IUTIII file; it must not be placed in the IUTII backend file.
G5. The layer/ownership issue: Example36SourceModelBackend.lean is an IUTII
    production file; adding P3 is a production edit requiring its owner and a
    targeted build. The new IUTIII file P4 is a separate production file.
G6. Source-object gap remains: OriginalInput has an arbitrary V and no
    identification of V/prime-strip/completion with the places/Frobenioid. C1g1
    only supplies the global Frobenioid at Fmod; it does not close group1's
    source-object/K2 gap.
G7. FrobenioidPresentation has no Prime/rho_v/Prop3.7 tuple data; the full
    Example 3.6(ii) source tuple cannot be stated from this presentation alone.
G8. No consumer currently imports a Frobenioid derived from OriginalInput
    (group1-STAGE1 section 6.2); C1/C10 must add that consumer only after P4.

## Migration / file plan

Recommended production order:

1. Edit LeanFormal/IUT/IUTII/Frobenioid/Example36SourceModelBackend.lean:
   - add import Iut.Foundations.SourceModelFrobenioidPresentation;
   - insert P1 and P2 after bottomBase_hom_eq_id (:59);
   - insert P3 after numberFieldSourceModelInput (:476).
   Owner: current backend production owner (not this C1g1 stage).
2. Add LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInputFrobenioidPresentation.lean
   containing P4, imports listed above, namespace Theorem311Source.
   Owner: C1 owner / N8 integration owner.
3. C1 imports the new P4 file and uses
   sourceOriginalInputFrobenioidPresentation I.
4. Do not edit tmp/sheaf/n8/Group1Statement.lean into production and do not
   import it.
5. Targeted builds after migration:
   - lake build LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
   - lake build LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInputFrobenioidPresentation
   - then C1's consumer build.
   Stage 1 does not run these; exact source versions to be recorded at migration.

Alternative acceptable plan: put P3 and P4 in one new IUTIII file importing the
backend and presentation, avoiding a second edit of the IUTII backend file.
P1/P2 must still live in the backend because BottomBase and its hom theorem are
there. The chosen plan must preserve layer direction: IUTII must not import
IUTIII.

## Status fields

- statement_compiles: not applicable (this stage writes no Lean).
- proof_body_checked: not applicable / not run.
- kernel_closed: not applicable.
- target_accepted: not run.
- exact production declarations to add: P1, P2, P3, P4 as above.
- no production file edited; tmp Group1Statement not imported.
- next action: production owner applies P1/P2/P3, then C1 owner adds P4; targeted
  build and consumer-wiring evidence follow at the migration stage.
