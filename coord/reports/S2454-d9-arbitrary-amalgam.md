# S2454: arbitrary amalgamation on the S2448 non-split cover — exact missing

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL retained:
- S2448GeneralCoverActual.lean: concrete non-split cover K=Q, S=Spec Q coprod Spec Q over Spec Q, coverPresieve_mem actual, not identity/maximal/split-epi. EXIT=0, olean 171072, SHA256 2EE1F709437CAF7E7D5226F426DDE872FFDE356B8730F8A2347CFE38D7780F7B.
- S2453NonSplitCanonicalAmalgamActual.lean: canonical descent datum Amalgam on that cover. EXIT=0, olean 21280, SHA256 53ea0cdcb66913ed42e27fafa95d035b711eabf8a2ee83a413552f811b454cf0.

ARBITRARY: not constructed. Exact first missing is
  S2448ConcreteAmalgam :=
    forall D : (S2029SheafPrestack K).DescentData (fun g : coverPresieve.category => g.obj.hom),
      Nonempty (Amalgam (S2029SheafPrestack K) (fun g : coverPresieve.category => g.obj.hom) D).
Equivalently HasEffectiveDescentPresieve at coverPresieve and the effective-descent half of IsStackFor.

Why Mathlib does not supply it:
- No Pseudofunctor.IsStack / IsStackFor instance for J.pseudofunctorOver (Type u); only the class, projections, and constructors taking the stack condition as a hypothesis.
- No coproduct-slice equivalence Over (X coprod Y) ~ Over X x Over Y to decompose the two-coproduct cover and glue the two slice sheaves.
- No general Cech descent/glue construction for objects of slice sheaves.
No arithmetic obstruction at this cover; the gap is the absent slice-topos gluing construction.

Subagent C (S2448) delivered the concrete cover and this exact missing; no arbitrary Amalgam file was delivered.

No S2152QIsStack claim. No fake, no sorry, no new axiom.