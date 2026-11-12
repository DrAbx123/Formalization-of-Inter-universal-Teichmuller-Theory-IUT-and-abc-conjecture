# SUBAGENT A REPORT -- S2979 effective descent (deep-audit group A)

Agent: subagent A (group A, task-699). Workspace: D:/lean (Windows, pwsh).
Date of final run: 2026-11-07 19:07 (Asia/Shanghai).
Deliverable source (new file): tmp/sheaf/xif/paper/S2979EffectiveDescentActual.lean
This report (new file): coord/SUBAGENT_A_REPORT.md
No existing source file was edited. No sorry, no axiom, no placeholder, no True,
no added hypotheses in the statements of the proved theorems.

## 0. Verification of the deliverable (final state)

Command run (workdir D:/lean):

    lake env lean -j1 -R 'D:/lean' tmp/sheaf/xif/paper/S2979EffectiveDescentActual.lean

    EXIT = 0
    source SHA256 = 279DC71F5BE0D857EB3D29F69599CD59FBD66CAC240D5FF76705875FA5344DC2
    source bytes = 16102
    source mtime = 2026-11-07 19:07:27

Olean: NOT produced. The file was checked with a direct "lake env lean" invocation,
which type-checks and elaborates but does not write .olean. I verified that neither
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S2979EffectiveDescentActual.olean
nor
  tmp/sheaf/xif/paper/S2979EffectiveDescentActual.olean
exists, so there is no olean SHA to report. The source SHA above is the artifact hash.

Axiom audit: every theorem in the file depends on exactly
  [propext, Classical.choice, Quot.sound]
(see section 5 for the verbatim #print axioms output). In particular there is no
sorryAx and no extra axiom in the closure of any theorem.

Honest labels for this package:
  statement_compiles   = YES (the whole file, EXIT 0; all statements elaborate)
  proof_body_checked   = YES for all 11 proved declarations (no error, no sorry)
  kernel_closed        = YES for the file's theorems (axioms as above)
  target_accepted      = NO. S2893A6QEffectiveDescent is NOT proved. The file proves
                         only conditional no-go theorems plus the exact reduction.
                         The target is expected to be FALSE; see sections 3-4.

## 1. Files read (all read-only)

Core target chain:
  tmp/sheaf/xif/paper/S2893A6QIsStackActual.lean
  tmp/sheaf/xif/paper/S2882A6PointwisePseudofunctorActual.lean
  tmp/sheaf/xif/paper/S2812IsStackActual.lean
Imported context and templating:
  tmp/sheaf/xif/paper/S2811IsPrestackActual.lean
  tmp/sheaf/xif/paper/S2810PrestackActual.lean (imported by the above chain)
  tmp/sheaf/xif/paper/S2813IsStackActual.lean (imported by the above chain)
  tmp/sheaf/xif/paper/S1971ActionStackificationActual.lean
  tmp/sheaf/xif/paper/S2993A6QIsStackNoGo.lean
  tmp/sheaf/xif/paper/S2903A6QEffectiveDescentActual.lean
  tmp/sheaf/xif/paper/S2909A6QDescentAttemptActual.lean
  tmp/sheaf/xif/paper/S2975A6QIsStackInhabitant.lean
  tmp/sheaf/xif/paper/S2977A6QIsStackActual.lean
  tmp/sheaf/xif/paper/S2994A6Stackification.lean
  tmp/sheaf/xif/paper/S2995A6StackificationActual.lean
  tmp/sheaf/xif/paper/S2996A6StackificationActual.lean
  tmp/sheaf/xif/paper/S2997A6StackificationActual.lean
Coordination/audit:
  coord/DEEP_AUDIT_ABC_IUT.md
  coord/DEEP_AUDIT_TASK_BOARD.md
  coord/AUDIT_LEDGER.md (entries 11845-11873)
Mathlib (for the exact API used):
  Mathlib/CategoryTheory/Sites/Descent/DescentData.lean
  Mathlib/CategoryTheory/Sites/IsSheafFor.lean
  Mathlib/CategoryTheory/Action.lean
  Mathlib/CategoryTheory/Elements.lean
  Mathlib/CategoryTheory/Bicategory/Functor/LocallyDiscrete.lean
  Mathlib/CategoryTheory/Category/Cat.lean
  Mathlib/CategoryTheory/ConcreteCategory/Basic.lean
  Mathlib/CategoryTheory/Types/Basic.lean

## 2. Exact first Lean error (verbatim) and its meaning

The mathematical first error is the failed S2812-style gluing step: a descent
datum only gives its hom up to the sign twist, and the untwisted compatible-family
equality requires that twist to be 1. The literal first Lean error met while
attacking this in the deliverable (first compile of this file, before the final
fix) was:

    tmp/sheaf/xif/paper/S2979EffectiveDescentActual.lean:173:2: error: Type mismatch: After simplification, term
      h
     has type
      @Eq ((actionAsFunctor SignGroup (Y -> X)).obj ((QA6.map f2.op.toLoc).toFunctor.obj (D.obj i2)).fst)
        ((ConcreteCategory.hom (fun x => (D.hom q f1 f2 hf1 hf2).val * x))
          ((QA6.map f1.op.toLoc).toFunctor.obj (D.obj i1)).snd)
        ((QA6.map f2.op.toLoc).toFunctor.obj (D.obj i2)).snd
     but is expected to have type
      @Eq (Y -> X) ((f1 * objBack (D.obj i1)) * S2882A6Aut (twistVal (D.hom q f1 f2 hf1 hf2))) (f2 * objBack (D.obj i2))

(In the real output the multiplication signs are category composition and the
function coercion uses the ConcreteCategory ofHom notation; the text above keeps
the ASCII rendering. The term displayed by Lean was the property of the Element
morphism and the expected type was the twisted equality of the descent family.)

The error shows both sides are the same equality up to definitional unfolding
(actionAsFunctor.obj, ActionCategory.back, the sign smul), but not up to the
syntactic normal form demanded by simp. The final file fixes it by proving the
twisted equality hom_twist_eq directly, using exactly the Elements-morphism
property (definitional equality at default transparency), and by making the
gluing lemma conditional on the twist being trivial.

A second, technical error was met in an earlier compile of this package while
trying to prove the canonical-twist lemma S2979CanonicalTwistTrivial (unfolding
Pseudofunctor.DescentData.ofObj and Pseudofunctor.mapComp'):

    The target expression is not type-correct under the instances transparency level
    Application type mismatch: the argument Y has type
      @Iut.SchemeOverField S2847A6.F ...
    but is expected to have type
      @Iut.SchemeOverField K ...

Reason: S2882A6Q is stated over K = S2844D6F6BaseChangeActual.K with S2882's
local Field K instance, while S2893's statement uses S2847A6.F. The two are
definitionally equal at default transparency (which is why S2893 compiles) but
not at the instances transparency used inside that strict-coherence simp. This
is a technical gap in the canonical-twist proof, not the mathematical obstruction.

## 3. The blocking missing lemma / missing object

(1) Formal lemma (expected TRUE, not proved here):
    S2979CanonicalTwistTrivial
      forall {U} (R : Sieve (Opposite.unop U.as)) (x : QA6.obj U)
        {Y} (q : Y -> Opposite.unop U.as) {i1 i2} (f1 : Y -> i1.obj.left)
        (f2 : Y -> i2.obj.left) (hf1 : f1 * i1.obj.hom = q) (hf2 : f2 * i2.obj.hom = q),
      twistVal (((QA6.toDescentData (fun i => i.obj.hom)).obj x).hom q f1 f2 hf1 hf2) = 1
    The canonical twist of toDescentData is an equality transport (S2882A6Q is a
    promoted strict functor), so this should be provable from
    Pseudofunctor.DescentData.ofObj's two mapComp' factors, Cat.Hom2.eqToHom_toNatTrans_app
    and S1971ActionCategory_eqToHom_val, but the unfolding currently breaks at
    Lean's instances transparency (see the second error above). A robust route is
    to prove a general lemma: any morphism in the fiber which is an equality
    transport of objects has twist 1, and then apply it to the two mapComp'
    components; this avoids global unfolding of the fiber instances.

(2) Missing geometric object (the real obstruction; NOT in the tree):
    S2979NontrivialSelfTwist
      exists (U) (R : Sieve U), R in etaleTopology K U,
        D : QA6.DescentData (fun i => i.obj.hom),
        i, Y, q : Y -> U, f1 f2 : Y -> i.obj.left,
        hf1 : f1 * i.obj.hom = q, hf2 : f2 * i.obj.hom = q,
        twistVal (D.hom q f1 f2 hf1 hf2) != 1
    Equivalently: a nontrivial etale SignGroup-torsor (SignGroup = Z/2) with an
    equivariant point, i.e. a connected nonsplit etale Z/2-cover with a point
    fixed by the sign involution alphaOverS2844. Natural candidates: a quadratic
    etale cover of Spec F (F contains sqrt(-1), so there are such covers of the
    constant etale site), or the [2]-cover of the A6 elliptic curve with a
    rational 2-torsion translation (the A6 curve has rational 2-torsion, S2826).
    Constructing this in the current API requires an actual nonsplit cover plus
    the fixed-point check, neither of which exists in the tree; S1971/S2993
    record the same trivial-sign-torsor obstruction.

Consequence: the target is expected to be FALSE, because nothing in the etale
site makes all SignGroup-torsors split. Treat group A as a no-go/stackification
reduction, and do not spend further effort trying to inhabit
S2893A6QEffectiveDescent directly. The correct positive object is the
stackification/quotient stack (deep-audit group B).

Important correctness note: the implication (canonical twist trivial + nontrivial
self-twist => not effective) is valid only in the self-twist case i1 = i2, because
then the comparison morphisms of an isomorphism of descent data are the same at
both ends. The naive two-index version is FALSE: for i1 != i2 the comparison
twists differ and the twist equation only gives
twist(D.hom) = h2 * twist(toDD.hom) * h1^-1
with h1 != h2 in general. The file therefore states twist_conj_of_iso only for a
single index i. This distinction is essential for anyone reusing these lemmas.

## 4. What is proved in the deliverable (no sorry/axiom)

Definitions/abbreviations: K, QA6 := S2882A6Q, Target := S2893A6QEffectiveDescent,
twistVal (group element of a fiber morphism), objBack (underlying site morphism of
a fiber object), S2979CanonicalTwistTrivial, S2979NontrivialSelfTwist.

Proved lemmas/theorems:
  back_map
    ((QA6.map g).toFunctor.obj P).back = g.as.unop * P.back
  objBack_map
    objBack ((QA6.map g).toFunctor.obj P) = g.as.unop * objBack P
  smul_eq_comp
    g . P = P * S2882A6Aut g
  twistVal_comp
    twistVal (phi * psi) = twistVal psi * twistVal phi
  twistVal_map
    twistVal ((QA6.map g).toFunctor.map phi) = twistVal phi
  hom_twist_eq
    (f1 * objBack (D.obj i1)) * S2882A6Aut (twistVal (D.hom q f1 f2 hf1 hf2))
      = f2 * objBack (D.obj i2)
    (the exact twisted equality; the key reduction)
  descentFamily (def)
    the underlying yoneda.obj X-valued compatible family of a descent datum
  descentFamily_compatible_of_twist_one
    if all twists of D are 1 then (descentFamily R D).Compatible
    (the exact S2812 gluing step; shows the twist is the only obstruction)
  twist_conj_of_iso
    for a self-twist (single index i), if D is isomorphic to toDescentData x via e,
    then twistVal (D.hom ...) =
      h * twistVal (toDD x).hom ... * h^-1 with h = twistVal (e.hom.hom i)
  not_effective_of_nontrivial_selfTwist
    S2979CanonicalTwistTrivial + twistVal (D.hom ...) != 1 =>
    D is not in the essential image of toDescentData
  not_target_of_twist
    S2979CanonicalTwistTrivial + S2979NontrivialSelfTwist => Not Target
  not_isStack_of_twist
    S2979CanonicalTwistTrivial + S2979NontrivialSelfTwist => Not S2893A6QIsStack

The two hypotheses of the no-go theorems are explicit hypotheses of the theorems,
not axioms: the file does not assert them. This is deliberately a conditional
no-go; the missing inputs are exactly the two items of section 3.

## 5. Verbatim #print axioms output of the final run

    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.back_map' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.objBack_map' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.smul_eq_comp' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.twistVal_comp' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.twistVal_map' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.hom_twist_eq' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.twist_conj_of_iso' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.not_effective_of_nontrivial_selfTwist' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.descentFamily_compatible_of_twist_one' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.not_target_of_twist' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual.not_isStack_of_twist' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]

## 6. Next executable step

Recommended (negative route, completes group A as a no-go):
  1. Prove S2979CanonicalTwistTrivial. Avoid the instances-transparency unfold:
     first prove, for P Q : QA6.obj U, that any morphism whose underlying
     Elements component is an equality transport has twist 1 (this is
     S1971ActionCategory_eqToHom_val transported through the fiber), then note
     that both factors of ofObj.hom are of that form (Cat.Hom2.eqToHom_toNatTrans_app
     plus F.mapComp' being eqToIso for the promoted strict functor
     S2882A6PFunctor, whose map_id/map_comp are rfl).
  2. Construct S2979NontrivialSelfTwist from a nonsplit connected etale Z/2-cover
     of Spec F with an alphaOverS2844-fixed point; in the A6 setting this is the
     [2]-cover of the A6 elliptic curve with a rational 2-torsion translation
     (S2826 gives the rational 2-torsion). This is geometric input, not linear
     algebra; it needs a concrete cover and its fixed point.
  3. Apply not_target_of_twist / not_isStack_of_twist. The exact check command for
     every step is:
       lake env lean -j1 -R 'D:/lean' tmp/sheaf/xif/paper/S2979EffectiveDescentActual.lean
  4. Record in AUDIT_LEDGER that S2893A6QEffectiveDescent is expected false and
     that group A reduces to the triviality of SignGroup-torsors; keep group B's
     stackification as the positive route.

Not recommended: trying to prove twist trivialization for all descent data. That
is exactly the missing torsor-splitting and is expected to be false.

## 7. Boundary conditions respected

  - Only the two new files were created/edited:
      tmp/sheaf/xif/paper/S2979EffectiveDescentActual.lean
      coord/SUBAGENT_A_REPORT.md
  - No existing source file was modified.
  - No sorry, axiom, placeholder, True, or fake assumption is used in the file.
  - The two no-go hypotheses are ordinary theorem parameters, clearly named, and
    the file proves no unconditional claim about the target.
