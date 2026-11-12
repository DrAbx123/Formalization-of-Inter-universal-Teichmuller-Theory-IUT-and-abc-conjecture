# S1192: is the S1188 product-lift invariantImage gap real?

Date: 2026-10-30. Report only; no new Lean.

## 1. The lemma in S1188

S1188 needs to lift S1184's factor isomorphism

```text
κv : TimesMuKummer.Isomorphism
  (upper.unitsAction v)
  ((lower.unitsAction v).comp (φ.isoPi v))
```

along

```text
eval v : (∀ w, upper.Pi w) →* upper.Pi v
```

to the product group `G = ∀ w, upper.Pi w`.  The invariant-image part needs

```text
fixedSubgroup (upper.unitsAction v) (H.map (eval v))
  = fixedSubgroup ((upper.unitsAction v).comp (eval v)) H
```

for every open subgroup `H ≤ G`, and similarly on the lower side.

## 2. Is it a real mathematical obstruction?

No.  It is an API lemma gap, not an incompatibility.

The general identity is elementary:

```text
fixedSubgroup (rho.comp f) H
  = fixedSubgroup rho (map f H)
```

because

```text
u ∈ fixedSubgroup (rho.comp f) H
  ↔ ∀ h ∈ H, rho (f h) u = u
  ↔ ∀ g ∈ f(H), rho g u = u
  ↔ u ∈ fixedSubgroup rho (f(H)).
```

Here `f = eval v`; it is a continuous group hom, and `eval v` is an open map
(`isOpenMap_eval` in Mathlib, Topology/Bases.lean).  Hence the image of an open
subgroup is an open subgroup, and the identity applies on both sides.

Therefore the product lift of `κv` is constructible; S1184 + this lemma
suffices.  No new Kummer data is needed.

## 3. What is actually missing in the tree

Mathlib has `OpenSubgroup.comap` but no `OpenSubgroup.map`.  So the exact
minimal Lean gap is:

```lean
def OpenSubgroup.mapOfOpenMap
    (H : OpenSubgroup G) (f : G →* N)
    (hf : Continuous f) (hopen : IsOpenMap f) : OpenSubgroup N where
  toSubgroup := (H : Subgroup G).map f
  isOpen' := by
    simpa [Subgroup.coe_map] using hopen _ H.isOpen
```

and then:

```lean
theorem fixedSubgroup_comp_eq_map
    (rho : H →* MulAut U) (f : G →* H) (Hopen : OpenSubgroup G) :
    TimesMuKummer.fixedSubgroup (rho.comp f) Hopen
      = TimesMuKummer.fixedSubgroup rho (Hopen.mapOfOpenMap f hf hopen)
```

Both are source-independent and should compile without arithmetic content.

## 4. Minimal feasible G

Two valid choices:

1. **Full product** `G := ∀ v, upper.Pi v` (minimal simple form).
   `factorUpper v := eval v`,
   `factorLower v := (φ.isoPi v).comp (eval v)`,
   `sourceUnits v := (upper.Mon v)ˣ`,
   `sourceAction v := (upper.unitsAction v).comp (eval v)`,
   `kappaUpper v := Isomorphism.refl`,
   `kappaLower v := S1184 κv lifted by the lemma above.
   This uses the full product topology and `isOpenMap_eval`.

2. **Graph subgroup**
   ```text
   G := { g : (v : V) → upper.Pi v × lower.Pi v |
          ∀ v, g v .2 = φ.isoPi v (g v .1) }
   ```
   with `factorUpper v := (eval v) ∘ projUpper`,
   `factorLower v := (eval v) ∘ projLower`; projections are isomorphisms, so
   the same fixed-subgroup lemma applies.  This is semantically closer to the
   strip link graph, but needs subtype topology and projection continuity.

Full product is minimal in Lean work; the graph choice is minimal in
semantics if one insists that upper/lower product factors be linked by
`φ.isoPi`.

## 5. What does NOT bypass it

Choosing `G := upper.Pi v` (single factor) avoids the product lift only if
`V` is a singleton.  For general `V`, a single factor cannot carry all
`factor v` maps, and choosing one `v0` plus arbitrary isomorphisms to other
factors would require actual group isomorphisms `upper.Pi v0 ≃* upper.Pi v`
not present from the strip link alone.

Using a non-surjective `G → upper.Pi v` does not help: the fixed-subgroup
identity depends only on the image subgroup, but the image need not be open
unless the map is open.  Evaluation/projection is open, so the full product
works; an arbitrary non-open map would be the wrong attempt.

## 6. Conclusion

- S1188's gap is **real as a missing API lemma**, but **not a mathematical
  obstruction** to the product lift.
- Minimal feasible group: `G = ∀ v, upper.Pi v` with evaluation maps, plus
  `OpenSubgroup.mapOfOpenMap` and `fixedSubgroup_comp_eq_map`.
- With these two lemmas, S1184 directly gives a non-refl `kappaLower`, hence a
  non-refl `SourceTimesMuKummerLayer` via `layerKummer`/`layerOfPair`.
- No S1187 is needed; no new arithmetic/Kummer data is needed.
- No new Lean written in this audit.
