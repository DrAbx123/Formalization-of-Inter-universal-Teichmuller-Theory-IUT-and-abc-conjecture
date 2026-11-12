# S2511: the point at infinity `[1:0]` of `P¹_UB` is constructed over `Spec UB`

Date: 2026-11-03.  Task E: construct

    S2511Point : S2508ResidueScheme ⟶ S2508FOver

as a morphism of `UB`-schemes (`Over (Spec UB)`), i.e. supply the `point` field of
`S2508CuspDatum` — or report the exact first missing / blocked triangle.

## Result (short)

**The point is constructed, unconditionally; the structure triangle is proved.  No
`sorry`, no `axiom`, no new hypothesis, no change of objects.**  All probed declarations
depend only on `[propext, Classical.choice, Quot.sound]`.

    file        tmp/sheaf/xif/paper/S2511InfinityPointUB.lean
    EXIT        0   (lake env lean -o <olean> <src>, serial, 2026-11-03 13:17)
    src bytes   10245   (241 lines)
    SHA256 src  19BE948E4C087270B96F1811A848948367FE81C584CCBF56F2C84946D15CC1DC
    olean       .lake/build/lib/lean/tmp/sheaf/xif/paper/S2511InfinityPointUB.olean
    olean bytes 136784
    SHA256 olean AC707C9A4E4C76D9463D3FE365FB8D4320675EA9BE8B481199341B5CA878F39B
    imports     tmp.sheaf.xif.paper.S2508CuspDataUB   (only)
    axioms      [propext, Classical.choice, Quot.sound] on every probed declaration
                (S2511phi0, S2511chart0, S2511pointChart, S2511pointMap,
                 S2511_ring_comp, S2511pointMap_structure, S2511Point, S2511Point_w)

## What is constructed

Locked target type (checked inside the file and again from the compiled olean by
`tmp/sheaf/xif/paper/_S2511Consumer.lean`, EXIT=0):

    #check S2511Point  ==>  S2511Point : S2508ResidueScheme ⟶ S2508FOver

Ring level, chart `X 0 ≠ 0` of `P¹_UB = Proj UB[X₀,X₁]` (route exactly as specified):

* `S2511X0 = MvPolynomial.X 0`, `S2511X0_mem : X 0 ∈ S2504Grading 1`
* `S2511phi0 : MvPolynomial (Fin 2) UB →+* UB := eval₂Hom (RingHom.id UB)
   (fun i => if i = 0 then 1 else 0)`   (the residue map of `[1:0]`)
* `S2511phi0_X0 : phi0 X0 = 1`; `S2511phi0_isUnit : IsUnit (phi0 X0)`
* `S2511chart0 : Away S2504Grading X0 →+* UB
    := (Localization.awayLift phi0 X0 _).comp
         (algebraMap (Away S2504Grading X0) (Localization.Away X0))`
* `S2511pointChart : Spec (of UB) ⟶ Spec (of (Away S2504Grading X0)) := Spec.map (ofHom chart0)`
* `S2511pointMap : Spec (of UB) ⟶ S2504P1 := pointChart ≫ Proj.awayι S2504Grading X0 X0_mem (by norm_num)`

Scheme level / slice level:

* `S2511pointMap_structure : S2511pointMap ≫ S2508FOver.hom = S2508ResidueScheme.hom`
  (**the triangle; not hypothetical**).  Proof: `S2508FOver_hom` (S2508) unfolds the
  structure morphism, `Proj.awayι_toSpecZero` collapses `awayι ≫ toSpecZero`, and the
  two `Spec.map`s collapse; the remaining ring identity is
* `S2511_ring_comp : chart0.comp (fromZeroRingHom.comp ((projZeroRingHom').comp C))
     = RingHom.id UB`,
  proved by `RingHom.ext` on `c : UB`: `projZeroRingHom'` fixes constants, the class of a
  constant is `Localization.mk (C c) 1`, and `awayLift_mk` at `j = 0` evaluates it to
  `phi0 (C c) = c`.
* `S2511Point : S2508ResidueScheme ⟶ S2508FOver := Over.homMk S2511pointMap S2511pointMap_structure`
* `S2511Point_left : S2511Point.left = S2511pointMap` (rfl)
* `S2511Point_w : S2511Point.left ≫ S2508FOver.hom = S2508ResidueScheme.hom` (`Over.w`)

Type locks present in the file (`example`s, all EXIT=0):

    example : S2508ResidueScheme ⟶ S2508FOver := S2511Point
    example : (Over.mk (𝟙 (Spec (CommRingCat.of UB)))) ⟶ S2504P1Over := S2511Point
    example : S2508ResidueScheme.left ⟶ S2508FOver.left := S2511Point.left
    example : S2511Point.left = S2511pointMap := S2511Point_left
    example : S2511Point.left ≫ S2508FOver.hom = S2508ResidueScheme.hom := S2511Point_w
    example : S2511pointMap ≫ S2508FOver.hom = S2508ResidueScheme.hom := S2511pointMap_structure

## Exact first missing after this packet

`S2508CuspDatum` is still not inhabited: with `point := S2511Point` supplied, exactly two
fields remain, in this order:

1. `separation : ∀ s : S2508ResidueScheme ⟶ S2508AffineOver, s ≫ S2508ChartOverMap ≠ S2511Point`
   — the scheme-level boundary condition (the chart `X 1 ≠ 0` misses `[1:0]`; this file
   lands the point in the *other* chart `X 0 ≠ 0`, so the two chart images are disjoint on
   the residue scheme, but the disjointness argument itself is not constructed here).
2. `stackOpenImmersion : Iut.EtaleStackOpenImmersion S2508StackOpenMap` (the 2-Yoneda
   representable-open-immersion property of the chart; iso-comma pullback witnesses are not
   in the tree, cf. S1864/S1913).

No type error and no blocked triangle: the whole route of the task went through; the only
issue encountered was a rewrite-association detail, fixed by unfolding `S2511pointChart`
before the second `← Spec.map_comp`.

## Reproduction

    lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2511InfinityPointUB.olean \
                  tmp/sheaf/xif/paper/S2511InfinityPointUB.lean      # EXIT=0

Serial compile only; no `lake build`, no cache, no parallelism.  Lexical scan of the source
finds no `sorry`, `admit`, `axiom`, `native_decide`, or `#eval` (the single textual match
for the word "sorry"/"axiom" is the module docstring's "No `sorry`, no `axiom`").
