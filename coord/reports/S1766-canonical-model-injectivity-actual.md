# S1766: R2a injectivity of the canonical identity-point model action

Layer: D6 orbicurve finite-etale cover category / canonical identity-point
affine model (S1733Model).

Source objects: S1728 cover type and 2-isomorphism quotient; S1733
identity-point base change and model; S1743 lift/section; S1744
S1744ModelMapOfCoverMap and S1744CanonicalModelHomActionActual; S1742
2-Yoneda comparison.

No sorry, no new axiom, no Shrink/PUnit, no ULift coercion of the
mathematical data (the only ULift occurrence is the proof-level ULift.ext for
Mathlib's Discrete hom representation).

## Question

S1744 isolated R2a: is the canonical action

  S1744ModelMapOfCoverMap A B : S1728CoverMap A B -> (S1733Model A --> S1733Model B)

injective?  S1744 suspected it might fail because the construction uses only
the identity point, so two cover maps differing away from that point could
have the same model morphism.  Task: prove/refute, and if false construct an
actual counterexample or identify the exact extra model data.

## Result

1. Kernel theorem (unconditional).  Writing

     S1766Phi A B f = ((toSource A) o f.map) o lift B,

   whose 2-Yoneda evaluation is the action (S1766_act_def), we prove

     S1766_act_eq_iff_coverMapRel:
       act f = act g  <->  S1728CoverMapRel f g,

   i.e. two cover maps have the same canonical model morphism iff their
   underlying strong transformations are 2-isomorphic.  Both directions use
   only S1743's already-proved section lift o toSource = id on the source and
   target covers and S1742's 2-Yoneda comparison.  The missing retraction half
   S1743SourceRetraction is NOT needed for this theorem.

2. The action descends to the 2-isomorphism quotient and is injective there:
   S1766QuotAct and S1766QuotAct_injective.  Thus the canonical action is
   exactly the 2-isomorphism quotient of cover maps.

3. Raw R2a is equivalent to discreteness:
   S1766_raw_injective_iff_discrete:
     S1744CanonicalModelHomActionInjective S1744CanonicalModelHomActionActual
       <-> S1766CoverMapDiscrete.
   Equivalently (S1766_coverMapDiscrete_iff), no two distinct strong
   transformations between cover sources are 2-isomorphic.  Since the second
   field commutes of a cover map is a subsingleton (the target stack is
   representable; S1766_commutes_subsingleton), a cover map is determined by
   its underlying strong transformation.

4. Counterexample shape.  An actual counterexample to R2a is exactly a pair
   A B and f != g of cover maps with f.map = g.map (2-isomorphic):
   S1766ActualCounterexample and
   S1766_not_injective_iff_actualCounterexample.  Any such pair gives the
   explicit collision S1766_collision.  The tree constructs no cover object,
   so no unconditional pair is exhibited here; the exact missing statement is
   S1766CoverMapDiscrete.

5. Correct small hom model.  The 2-isomorphism quotient, realised as

     S1766QuotSmallCarrier A B = Set.range (S1766QuotAct A B),

   is Type 0 and equivalent to the genuine quotient (S1766QuotSmallEquiv).
   This is the small hom family for the actual cover category.  The raw-map
   target of S1733AffineCoverModel.homEquiv is the wrong shape unless the
   discreteness certificate S1766CoverMapDiscrete is added.

6. Correction of the S1744 reading.  The identity point of S1733 is the
   identity 1-cell of the base stack, so the identity-point base change is the
   identity base change; S1743's section shows that the model maps onto the
   whole cover source.  The action does not lose non-2-isomorphic data: its
   kernel is exactly 2-isomorphism.  Recording more test points cannot repair
   raw injectivity, because any functorial action is constant on 2-isomorphism
   classes; it can only help R2b/surjectivity.  The formal gap behind source
   representability is that EtaleStackBaseChangePresentation.isPullback is only
   a weak two-pullback witness (no one-cell uniqueness, no inverse 2-cell).

## Evidence

- Lean: tmp/sheaf/xif/paper/S1766CanonicalModelInjectivityActual.lean
  (670 lines, 30748 bytes,
  SHA256 CA8092D883E777A19FC41523D9D20FA624E551D88FF8D558C8E40B35139151E3).
- Build: lake env lean -o
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1766CanonicalModelInjectivityActual.olean
  tmp/sheaf/xif/paper/S1766CanonicalModelInjectivityActual.lean
  EXIT=0, no warnings, no sorryAx.
- Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1766CanonicalModelInjectivityActual.olean
  (194168 bytes, SHA256
  9CF748968DE39426F17E2151767C9C1F5C2760227483E31FACC4B221F6A3E20C).
- Axiom audit: every #print axioms in the file reports only propext,
  Classical.choice and Quot.sound.
- Scratch probe files used during development were deleted; only the module
  above remains.

## Statement / closure status

- statement_compiles = yes (target types written out for the actual
  S1728Cover, S1728CoverMap, S1733Model and the canonical action).
- proof_body_checked = yes for all theorems listed above.
- kernel_closed = yes (axiom trio only).
- target_accepted = false: OrbicurveEtaleFundamentalGroup is not constructed;
  R2b/surjectivity and the Galois-category structure remain open.

## Consumer

S1733/S1744 direct route to a small cover category and S1728's
S1728SmallRawCoverDataRequired.  S1766 supplies, unconditionally, a Type-0
hom model for the 2-isomorphism quotient and isolates the exact raw-map
discreteness gap; it also shows that S1743SourceRetraction is not needed for
the injectivity half.

## Next executable step

Either (a) construct a cover of the S1726 orbicurve carrying a nontrivial
2-isomorphism class of cover maps, which by S1766_collision refutes raw R2a,
or (b) prove S1766CoverMapDiscrete by strengthening the two-pullback witness
with one-cell uniqueness / an explicit retraction toSource o inv = id and
deriving representability/discreteness of cover sources.  R2b is independent
and remains the descent/surjectivity gap.
