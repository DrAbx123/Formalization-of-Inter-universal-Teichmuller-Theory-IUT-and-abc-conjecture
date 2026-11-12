# Subagent B report — deep-audit group B (D / atBase / generator_identification / W)

Date: 2026-11-07. Workspace: D:/lean. Operator: subagent B (parent baa72c29-948b-4d87-8bca-d6d61e7e58f5).

New files (only these two are left by this task):

* tmp/sheaf/xif/paper/S2980QuotientStackActual.lean — actual constructions + machine-checked no-go;
* coord/SUBAGENT_B_REPORT.md — this report.

No existing source file was edited. Temp probe files used to capture errors were deleted.

## 0. Bottom line

1. **D, atBase and generator_identification are ACTUAL and constructed here** (fresh compile EXIT=0; axioms exactly the allowed trio). The demanded object is

   `D : Pseudofunctor Iut.SignActionIndex (Iut.EtaleStackPseudofunctor S2847A6.F)`,
   `D.obj signActionObject = S2855HyperbolicOrbicurve.stack.fiber` (the representable etale stack of the A6 curve `S2844X`),
   `D.map signActionGenerator = S2857StackAuto alphaOverS2844` (the actual elliptic involution),
   `atBase =` identity adjoint equivalence, `generator_identification =` a unitor isomorphism.

2. **This D is the sign-action diagram on the source curve X_F, not the quotient stack [X_F/sign].** The type of `atBase` in the corrected core forces `D.obj signActionObject ≌ S2855HyperbolicOrbicurve.stack.fiber`, and the latter is the representable stack of `S2844X`; it is not the quotient `cF = S2891CF hQ` (the sign action is not free: the elliptic involution has fixed points). The deep-audit wording "construct the quotient stack D" conflates two different objects. The quotient object is the separate input `Q` / a stackification of `Q`.

3. **W is blocked at its first input `hQ`, and `hQ` is not merely unproved — it is REFUTED.** The tree contains an unconditional no-go:

   * `S2975bA6QPresheafHomSheaf.S2975b_not_isStack : ¬ S2882A6Q.IsStack (etaleTopology K)` (empty-base obstruction: the hom presheaf of `S2882A6Q` is not a sheaf on the empty scheme);
   * `S2993A6QIsStackNoGo.S2993_not_isStack` re-exports it, and `S2993_not_isPrestack` proves the pointwise `Q` is not even a prestack.

   Hence `S2870QuotientWitnessData S2882A6Q hQ A` is vacuous; the deliverable proves `S2980W_vacuous` (any hypothetical W yields `False`).

4. Therefore the corrected core's input list `(hQ, D, atBase, generator_identification, W, I)` cannot be filled as stated: its first argument is false. **W was not constructed and must be restated for a stackification `Q'` of `S2882A6Q`.**

## 1. Exact first missing type / field / instance

Dependency order of the group-B target (see S2870A6CFPathAudit, S2892CoreWithQActual, S2905CoreWithHqW):

* `D`, `atBase`, `generator_identification`: sign-action data on X_F. **Constructed (this file).**
* `hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology F)`: **the first missing input; refuted**, not just unproved.
* `W.quotient : OrbicurveSignInvariantMorphism A (S2891CF hQ)`: the quotient morphism to the pointwise quotient. It cannot exist without `hQ`; granting `hQ`, it has no supplier in the tree (the pointwise action groupoid is not a stack quotient).
* `W.quotientWitness : OrbicurveSignQuotientWitness A quotient`: bicategorical universal property, a further separate obligation with no supplier.
* corrected stackification `Q'` with `Q'.IsStack` and a fiber equivalence to `S2882A6Q`: the real missing object for the paper-level quotient. S2994/S2996/S2995 contain only specifications/targets; no `Q'` is constructed in the tree. (S2996A6StackWitnessCore only re-uses `S2882A6Q` itself.)

## 2. Attempted construction (what typechecks)

File: tmp/sheaf/xif/paper/S2980QuotientStackActual.lean (288 lines).

Actual declarations (all no sorry / no axiom / no placeholder):

| declaration | type / content |
|---|---|
| `S2980X` | `S2844X : SchemeOverField S2847A6.F` |
| `S2980Q` | `S1742YS S2980X`, the representable etale stack |
| `S2980FiberEq` | `S2855HyperbolicOrbicurve.stack.fiber = S2980Q` (rfl) |
| `S2980SigMapOf` | `SignGroup → (S2980Q ⟶ S2980Q)`, `g ↦ S1742StrongTransOfHom (S2882A6Aut g)` |
| `S2980D` | pseudofunctor `SignActionIndex ⥤ᵖ EtaleStackPseudofunctor S2847A6.F`; object `S2980Q`, generator the actual involution, all 2-cell coherences by the 2-cell subsingleton of the representable stack |
| `S2980AtBase` | `S2980D.obj signActionObject ≌ S2855HyperbolicOrbicurve.stack.fiber` (identity adjoint equivalence) |
| `S2980D_map_generator` | `S2980D.map signActionGenerator = S2857StackAuto alphaOverS2844` |
| `S2980GeneratorIdentification` | `(S2980AtBase.inv ≫ S2980D.map signActionGenerator) ≫ S2980AtBase.hom ≅ S2857StackAuto alphaOverS2844` |
| `S2980A` | `Iut.OrbicurveSignAction S2855HyperbolicOrbicurve := S2869SignAction S2980D S2980AtBase S2980GeneratorIdentification` (actual consumer value) |
| `S2980NotHQ` | `¬ S2882A6Q.IsStack (etaleTopology S2847A6.F)` |
| `S2980NotPrestack` | `¬ S2882A6Q.IsPrestack (etaleTopology S2847A6.F)` |
| `S2980W_vacuous` | `∀ (A) (hQ) (W : S2870QuotientWitnessData S2882A6Q hQ A), False` |

Proof route for D (all actual): `S2882A6Aut` and its multiplication law; locale-discrete composition lemma `(f ≫ g).as = g.as * f.as` via `LocallyDiscrete.comp_as` + `SingleObj.comp_as_mul`; unit and composition coherences via the 2-Yoneda round trip `S1742HomOfStrongTrans_strongTransOfHom` / `S1742StrongTransIsoOfHom`; all higher 2-cell fields via discreteness of the representable value categories.

## 3. Exact first Lean error (W attempt)

A temporary probe (deleted; content quoted) imported the deliverable and attempted W. The first error is on the missing instance:

```lean
-- line 27 of the probe
example : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F) := by
  infer_instance
```

verbatim output:

```
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Pseudofunctor.IsStack S2882A6Q (Iut.SchemeOverField.etaleTopology S2847A6.F)
```

goal: `⊢ Pseudofunctor.IsStack S2882A6Q (Iut.SchemeOverField.etaleTopology S2847A6.F)`.

Granting `hQ` as a hypothesis, the first field of W is also unsolved (line 34 of the probe, `quotient := by done`):

```
error: unsolved goals
hQ : Pseudofunctor.IsStack S2882A6Q (Iut.SchemeOverField.etaleTopology S2847A6.F)
⊢ Iut.OrbicurveSignInvariantMorphism S2980A (S2870CF S2882A6Q hQ)
```

and the universal-property field (line 36) is

```
error: unsolved goals
hQ : Pseudofunctor.IsStack S2882A6Q (Iut.SchemeOverField.etaleTopology S2847A6.F)
⊢ Iut.OrbicurveSignQuotientWitness S2980A sorry
```

(the `sorry` in the last display is Lean's placeholder for the previous failed field, not a term in the deliverable).

Since `hQ` is refuted by `S2980NotHQ` (= S2993_not_isStack), these goals cannot be closed; W as specified is impossible, not just open.

## 4. Fresh compile / acceptance

Command (fresh, from D:/lean):

```powershell
lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2980QuotientStackActual.olean tmp/sheaf/xif/paper/S2980QuotientStackActual.lean
```

* EXIT = 0.
* Source: tmp/sheaf/xif/paper/S2980QuotientStackActual.lean
  * size 14649 bytes, 288 lines
  * SHA256 `916299C689DA292D7071B255F9A4B55ABF1E357388157E9D0C7B7171CAC6621D` (SHA8 `916299C6`)
* Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S2980QuotientStackActual.olean
  * size 175528 bytes
  * SHA256 `A14E19B6B9EB17B83F9255FBF2A4839DE9DD3C5924EE54DA906D2B578682A7D9` (SHA8 `A14E19B6`)
* `#print axioms` (verbatim from the fresh compile):

```
'S2980FiberEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'S2980D' depends on axioms: [propext, Classical.choice, Quot.sound]
'S2980AtBase' depends on axioms: [propext, Classical.choice, Quot.sound]
'S2980D_map_generator' depends on axioms: [propext, Classical.choice, Quot.sound]
'S2980GeneratorIdentification' depends on axioms: [propext, Classical.choice, Quot.sound]
'S2980A' depends on axioms: [propext, Classical.choice, Quot.sound]
'S2980NotHQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'S2980W_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* `#check` target types (verbatim):

```
S2980D : Iut.SignActionIndex ⥤ᵖ Iut.EtaleStackPseudofunctor S2847A6.F
S2980AtBase : S2980D.obj Iut.signActionObject ≌ S2855HyperbolicOrbicurve.stack.fiber
S2980GeneratorIdentification :
  (S2980AtBase.inv ≫ S2980D.map Iut.signActionGenerator) ≫ S2980AtBase.hom ≅ S2857StackAuto alphaOverS2844
S2980A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve
S2869SignAction S2980D S2980AtBase S2980GeneratorIdentification : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve
S2980NotHQ : ¬ Pseudofunctor.IsStack S2882A6Q (Iut.SchemeOverField.etaleTopology S2847A6.F)
S2980W_vacuous (A) (hQ) (W : S2870QuotientWitnessData S2882A6Q hQ A) : False
```

Supporting no-go artifacts (for the parent's acceptance record):

* S2975bA6QPresheafHomSheaf: source SHA256 `E919659A3619453E460A236EC75F7C7C8E6DE0C29FD2879CEF15373E9DCE99F6`; olean SHA256 `958C7AAA65849EA8313F6B62BA374D8C21250B29E1BDF655613AEDC64619CA18` (148416 B).
* S2993A6QIsStackNoGo: source SHA256 `526C6ED66F0B598AA9F10B97ABCE67D45BE2167FD4A7BB7BC415CCCC693765F9`; olean SHA256 `6E70572D24DD6F58A8EB1E0D805F795A7E3C156CA6DA7CB3533BBC19DB3881D5` (106808 B).
* S2893A6QIsStackActual: source SHA256 `AFD175B530A907AB4B00E56A629E37D0D7A05D478A8EC0D3DA2678D6E64FDFC9`; olean SHA256 `CF79236275058D5FAC7DF2173478B6572A94F98C49BE9A621EE765E793431A6A` (27888 B).

Classification: `statement_compiles` yes; `proof_body_checked` yes for the declarations above (EXIT=0, axioms trio); `kernel_closed` yes for those declarations; `target_accepted` NO — the group-B target W is not constructed and is impossible as stated (hQ false). D/atBase/generator_identification are actual but are not the quotient stack.

## 5. What this changes for the parent

1. Do not spend a task on "construct D": it is done (and independent of Q/stackification; reusable verbatim).
2. Do not spend a task on "prove hQ" or "construct IsStack S2882A6Q": it is refuted by S2975b/S2993. The corrected core's first argument must change.
3. The corrected route is forced to be route 3: replace `S2882A6Q` by a stackification `Q'` (= torsor/action stack), prove `IsStack Q'`, prove a fiberwise equivalence `Q' ≃ S2882A6Q`, and restate `S2870QuotientWitnessData` / `S2905Core` with `Q'` and `hQ'`. `S2980D`, `S2980AtBase`, `S2980GeneratorIdentification`, `S2980A` are unchanged by that replacement.
4. Concrete next executable step: construct `Q'` and its `IsStack`. In the tree the missing fields are isolated by S2994A6Stackification/S2996A6StackWitnessConstruction/S2995A6StackWitnessSpec: `Q'` with pointwise action-groupoid fibers, `IsPrestack`, `IsStack`, and `fiberEquiv` to `S2882A6Q`. The first concrete lemma to discharge is the prestack hom-presheaf sheaf condition for the stackified fiber, then effective descent (S2976b/S2993 isolate the failure of the pointwise `Q` on the empty base).

## 6. Honest status

* D / atBase / generator_identification / S2980A: ACTUAL (fresh compile, trio axioms).
* W: NOT constructed. Its first input `hQ` is false (S2993_not_isStack), so the W type is vacuous. The first exact Lean error at the attempt is the failed synthesis quoted in section 3.
* No completion of deep-audit group B is claimed.
