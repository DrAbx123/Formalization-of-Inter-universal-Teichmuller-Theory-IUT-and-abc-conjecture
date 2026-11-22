import tmp.sheaf.xif.paper.S2011Cor110bActual

/-!
# S2016: the `G_v`-equivariance of the actual Kummer map

Layer: **O** (original Theta-link / q-pilot).  Consumer: the S2011 package
(tmp/sheaf/xif/paper/S2011Cor110bActual.lean), whose missing item (M7)
is exactly the statement proved here, and through it the
[AbsTopIII] Corollary 1.10, (d) comparison in
tmp/sheaf/xif/paper/S2000CohomologicalPsiCnsActual.lean.

## The statement

S2011 constructs the action

  germAction p : G_v ->* MulAut (PsiCnsCohomology p)

of the local absolute Galois group `G_v = Gal(Qbar_p / Q_p)` on the actual
cohomological limit `lim_J H^1(J, mu_hat^Z)`, by translating a cocycle germ
along `g` (the open subgroup is conjugated, the coefficient values are acted
on).  S2000 constructs the actual Kummer map

  PsiCnsKummer p : O^tri -> PsiCnsCohomology p,

whose germ is the canonical compatible-root-system realization of the local
integral value.  The statement proved in this file is the equivariance

  PsiCnsKummer p (g . a) = germAction p g (PsiCnsKummer p a),      (M7)

for every `g` in `G_v` and every nonzero integral `a`, where `g . a` is the
genuine Galois action `LocalIntegralMonoid.galoisAction p g a` on the actual
nonzero integral closure of the valuation ring of `Q_p` inside `Qbar_p`.

## The proof

The concrete route stated in S2011 is carried out, with no new interface:

1. **Transport of a root realization.**  Given an integral Kummer root
   realization `R` of `a` over an open subgroup `U` fixing `a`, and `g` in
   `G_v`, define the transported realization `transportRealization R g` of
   `g . a` over the conjugated open subgroup `g U g^{-1}`: its root system is
   the `g`-translate of the root system of `R` inside the Grothendieck group,
   and its integral-unit ratio is `g . (ratio of the conjugate element)`.
   The ratio identity is exactly the cocycle law of the groupification action
   together with `k = g^{-1} h g` for `h` in `g U g^{-1}`.

2. **The transported cocycle is the translate.**  On the common open domain
   `g U g^{-1}` the cocycle of `transportRealization R g` is literally the
   cocycle `x |--> g . c(g^{-1} x g)` of `translateRep p g R.representative`;
   the two germ representatives are equivalent with identity coboundary.

3. **Root-choice independence removes the chosen roots.**  The canonical
   realization of `g . a` and the transported realization of `a` are two
   compatible root realizations of the *same* value, so their germs agree by
   `IntegralKummerRootRealization.germ_eq`.

4. Composing 1-3 gives `PsiCnsKummer_equivariant`.

## Not claimed

Nothing in [AbsTopIII] Corollary 1.10 (a)-(c) is added: the group-theoretic
reconstruction of `mu_hat^Z(G_v)`, the `H^2`-normalization, and the normalized
surjection remain the missing items (M1)-(M4) of S2011.  This file only closes
(M7), the equivariance of the actual Kummer map under the action S2011 did
construct.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.checkUnivs false

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual

namespace LeanFormal.IUT.XiFPaper.S2016KummerEquivarianceActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. The mono-analytic action, in the forms used below -/

/-- The action of `G_v` on the actual nonzero integral monoid `O^tri`,
i.e. the mono-analytic local `TM` action.  By construction this is the
genuine Galois action `LocalIntegralMonoid.galoisAction p g`. -/
abbrev monoAction (g : LocalAbsoluteGalois p) : MulAut (Otri p) :=
  (monoAnalytic p).action p g

/-- The induced action of `G_v` on the Grothendieck groupification. -/
abbrev monoGroupAction (g : LocalAbsoluteGalois p) :
    MulAut (LocalGroupification p) :=
  (monoAnalytic p).groupificationAction p g

/-- The induced action of `G_v` on the integral units. -/
abbrev monoUnitAction (g : LocalAbsoluteGalois p) : MulAut (Otri p)ˣ :=
  (monoAnalytic p).unitAction p g

theorem monoAction_galoisAction (g : LocalAbsoluteGalois p) (a : Otri p) :
    monoAction p g a = LocalIntegralMonoid.galoisAction p g a :=
  rfl

theorem monoAction_mul_apply (g h : LocalAbsoluteGalois p) (a : Otri p) :
    monoAction p (g * h) a = monoAction p g (monoAction p h a) := by
  have hmul : monoAction p (g * h) = monoAction p g * monoAction p h :=
    map_mul ((monoAnalytic p).action p) g h
  have hx := congrArg (fun e : MulAut (Otri p) => e a) hmul
  simpa [MulAut.mul_apply] using hx

theorem monoGroupAction_mul_apply (g h : LocalAbsoluteGalois p)
    (x : LocalGroupification p) :
    monoGroupAction p (g * h) x = monoGroupAction p g (monoGroupAction p h x) := by
  have hmul : monoGroupAction p (g * h) = monoGroupAction p g * monoGroupAction p h :=
    map_mul ((monoAnalytic p).groupificationAction p) g h
  have hx := congrArg (fun e : MulAut (LocalGroupification p) => e x) hmul
  simpa [MulAut.mul_apply] using hx

theorem monoGroupAction_of (g : LocalAbsoluteGalois p) (a : Otri p) :
    monoGroupAction p g (Algebra.GrothendieckGroup.of a) =
      Algebra.GrothendieckGroup.of (monoAction p g a) :=
  groupificationActionMulAut_of p (monoAnalytic p) g a

theorem monoUnitAction_apply (g : LocalAbsoluteGalois p) (u : (Otri p)ˣ) :
    monoUnitAction p g u = Units.map (monoAction p g).toMonoidHom u :=
  rfl

/-- The integral-unit embedding into the groupification is equivariant. -/
theorem unitGrothendieck_monoUnitAction (g : LocalAbsoluteGalois p) (u : (Otri p)ˣ) :
    unitGrothendieckHom p (monoUnitAction p g u) =
      monoGroupAction p g (unitGrothendieckHom p u) :=
  (unitGrothendieckHom_action p (monoAnalytic p) g u).symm

/-- The coefficient action of S2011 is the mono-analytic unit action,
evaluated pointwise. -/
theorem coefficientAction_act_apply (g : LocalAbsoluteGalois p)
    (cyclotome : PsiCnsCyclotome p) (q : Multiplicative (AddCircle (1 : ℚ))) :
    (PsiCnsCoefficientAction p).act g cyclotome q =
      monoUnitAction p g (cyclotome q) :=
  rfl

/-! ## 2. Transporting an integral Kummer root realization along `G_v` -/

/-- **The transported root realization.**  Conjugating the open subgroup and
translating the compatible root system along `g` produces an integral Kummer
root realization of `g . a` over `g U g^{-1}`. -/
noncomputable def transportRealization
    {U : OpenSubgroup (LocalAbsoluteGalois p)} {a : Otri p}
    (g : LocalAbsoluteGalois p)
    (R : IntegralKummerRootRealization p (monoAnalytic p) U a) :
    IntegralKummerRootRealization p (monoAnalytic p) (conjOpen p g U)
      (monoAction p g a) where
  fixed h := by
    let hv : LocalAbsoluteGalois p := h.1
    have hmem : conjHom p g⁻¹ hv ∈ U := h.property
    let k : U := ⟨conjHom p g⁻¹ hv, hmem⟩
    have hkg : (k : LocalAbsoluteGalois p) = g⁻¹ * hv * g := by
      show conjHom p g⁻¹ hv = g⁻¹ * hv * g
      rw [conjHom_apply p g⁻¹]
      group
    have hh : hv * g = g * (k : LocalAbsoluteGalois p) := by
      rw [hkg]
      group
    calc monoAction p hv (monoAction p g a)
        = monoAction p (hv * g) a :=
          (monoAction_mul_apply p hv g a).symm
      _ = monoAction p (g * (k : LocalAbsoluteGalois p)) a := by rw [hh]
      _ = monoAction p g (monoAction p (k : LocalAbsoluteGalois p) a) :=
          monoAction_mul_apply p g (k : LocalAbsoluteGalois p) a
      _ = monoAction p g a := by rw [R.fixed k]
  rootSystem :=
    { roots :=
        { toFun := fun q =>
            Additive.ofMul
              (monoGroupAction p g (R.rootSystem.roots q).toMul)
          map_zero' := by
            apply Additive.toMul.injective
            change monoGroupAction p g (R.rootSystem.roots 0).toMul = 1
            have hzero : (R.rootSystem.roots 0).toMul = 1 :=
              congrArg Additive.toMul (R.rootSystem.roots.map_zero)
            rw [hzero, map_one]
          map_add' := by
            intro first second
            apply Additive.toMul.injective
            change
              monoGroupAction p g (R.rootSystem.roots (first + second)).toMul =
                monoGroupAction p g (R.rootSystem.roots first).toMul *
                  monoGroupAction p g (R.rootSystem.roots second).toMul
            have hadd : (R.rootSystem.roots (first + second)).toMul =
                (R.rootSystem.roots first).toMul *
                  (R.rootSystem.roots second).toMul :=
              congrArg Additive.toMul (R.rootSystem.roots.map_add first second)
            rw [hadd, map_mul] }
      root_one := by
        apply Additive.toMul.injective
        change
          monoGroupAction p g (R.rootSystem.roots 1).toMul =
            Algebra.GrothendieckGroup.of (monoAction p g a)
        have hone : (R.rootSystem.roots 1).toMul =
            Algebra.GrothendieckGroup.of a :=
          congrArg Additive.toMul R.rootSystem.root_one
        rw [hone, monoGroupAction_of] }
  ratioUnit h q :=
    monoUnitAction p g
      (R.ratioUnit ⟨conjHom p g⁻¹ (h.1 : LocalAbsoluteGalois p), h.property⟩ q)
  ratio_spec h q := by
    let hv : LocalAbsoluteGalois p := h.1
    have hmem : conjHom p g⁻¹ hv ∈ U := h.property
    let k : U := ⟨conjHom p g⁻¹ hv, hmem⟩
    have hrat : R.ratioUnit ⟨conjHom p g⁻¹ (h.1 : LocalAbsoluteGalois p), h.property⟩ q
        = R.ratioUnit k q := rfl
    have hkg : (k : LocalAbsoluteGalois p) = g⁻¹ * hv * g := by
      show conjHom p g⁻¹ hv = g⁻¹ * hv * g
      rw [conjHom_apply p g⁻¹]
      group
    have hgk : g * (k : LocalAbsoluteGalois p) = hv * g := by
      rw [hkg]
      group
    change
      unitGrothendieckHom p
          (monoUnitAction p g
            (R.ratioUnit ⟨conjHom p g⁻¹ (h.1 : LocalAbsoluteGalois p), h.property⟩ q)) =
        monoGroupAction p (h.1 : LocalAbsoluteGalois p)
            (monoGroupAction p g (R.rootSystem.roots q).toMul) /
          monoGroupAction p g (R.rootSystem.roots q).toMul
    rw [hrat, unitGrothendieck_monoUnitAction, R.ratio_spec k q,
      map_div (monoGroupAction p g)]
    congr 1
    rw [← monoGroupAction_mul_apply p g (k : LocalAbsoluteGalois p)
        (R.rootSystem.roots q).toMul,
      hgk, monoGroupAction_mul_apply p hv g
        (R.rootSystem.roots q).toMul]

/-- The germ of the transported realization is the translate of the germ. -/
theorem transportRealization_germ
    {U : OpenSubgroup (LocalAbsoluteGalois p)} {a : Otri p}
    (g : LocalAbsoluteGalois p)
    (R : IntegralKummerRootRealization p (monoAnalytic p) U a) :
    (transportRealization p g R).germ = translateGerm p g R.germ := by
  apply Quotient.sound
  refine Iut.ContinuousH1GermRepresentative.Equivalent.of_equal_on
    (conjOpen p g U) le_rfl le_rfl ?_
  intro t
  apply MonoidHom.ext
  intro circle
  let additiveCircle : AddCircle (1 : ℚ) := circle.toAdd
  change
    (translateRep p g R.representative).cocycle t
        (Multiplicative.ofAdd additiveCircle) =
      (transportRealization p g R).representative.cocycle t
        (Multiplicative.ofAdd additiveCircle)
  induction additiveCircle using Quotient.inductionOn with
  | _ q =>
      rw [translateRep_cocycle_apply, coefficientAction_act_apply]
      change
        monoUnitAction p g
            (R.ratioUnit
              ⟨conjHom p g⁻¹ (t.1 : LocalAbsoluteGalois p), t.property⟩ q) =
          monoUnitAction p g
            (R.ratioUnit
              ⟨conjHom p g⁻¹ (t.1 : LocalAbsoluteGalois p), t.property⟩ q)
      rfl

/-- **Root-choice independence, applied.**  The canonical realization of the
translated value and the transport of the canonical realization of the
original value have the same germ. -/
theorem transportRealization_canonical_germ (g : LocalAbsoluteGalois p) (a : Otri p) :
    (canonicalIntegralKummerRootRealization p (monoAnalytic p)
        (monoAction p g a)).germ =
      (transportRealization p g
        (canonicalIntegralKummerRootRealization p (monoAnalytic p) a)).germ :=
  IntegralKummerRootRealization.germ_eq _ _

/-! ## 3. (M7): the equivariance of the actual Kummer map -/

/-- **Missing item (M7) of S2011 is proved.**  The actual Kummer map is
`G_v`-equivariant for the action `germAction` on the cohomological limit and
the Galois action on `O^tri`. -/
theorem PsiCnsKummer_equivariant (g : LocalAbsoluteGalois p) (a : Otri p) :
    PsiCnsKummer p (monoAction p g a) =
      germAction p g (PsiCnsKummer p a) := by
  have stepOne : PsiCnsKummer p (monoAction p g a) =
      (canonicalIntegralKummerRootRealization p (monoAnalytic p)
        (monoAction p g a)).germ := rfl
  have stepTwo : (canonicalIntegralKummerRootRealization p (monoAnalytic p)
        (monoAction p g a)).germ =
      (transportRealization p g
        (canonicalIntegralKummerRootRealization p (monoAnalytic p) a)).germ :=
    IntegralKummerRootRealization.germ_eq _ _
  have stepThree : (transportRealization p g
        (canonicalIntegralKummerRootRealization p (monoAnalytic p) a)).germ =
      translateGerm p g
        (canonicalIntegralKummerRootRealization p (monoAnalytic p) a).germ :=
    transportRealization_germ p g _
  have stepFour : translateGerm p g
        (canonicalIntegralKummerRootRealization p (monoAnalytic p) a).germ =
      translateGerm p g (PsiCnsKummer p a) := rfl
  exact stepOne.trans (stepTwo.trans (stepThree.trans (stepFour.trans
    (germAction_apply p g (PsiCnsKummer p a)).symm)))

/-- The same equivariance, written with the literal Galois action
`LocalIntegralMonoid.galoisAction` on `O^tri`. -/
theorem PsiCnsKummer_galoisAction (g : LocalAbsoluteGalois p) (a : Otri p) :
    PsiCnsKummer p (LocalIntegralMonoid.galoisAction p g a) =
      germAction p g (PsiCnsKummer p a) :=
  PsiCnsKummer_equivariant p g a

/-- Consequence for the image: the actual Kummer image of `O^tri` is stable
under the `G_v`-action on the cohomological limit. -/
theorem germAction_mem_kummerImage (g : LocalAbsoluteGalois p)
    {x : PsiCnsCohomology p} (hx : x ∈ PsiCnsKummerImage p) :
    germAction p g x ∈ PsiCnsKummerImage p := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨monoAction p g a, PsiCnsKummer_equivariant p g a⟩

/-! ## 4. Axiom probes -/

#print axioms monoAction_mul_apply
#print axioms monoGroupAction_mul_apply
#print axioms monoGroupAction_of
#print axioms unitGrothendieck_monoUnitAction
#print axioms transportRealization
#print axioms transportRealization_germ
#print axioms transportRealization_canonical_germ
#print axioms PsiCnsKummer_equivariant
#print axioms PsiCnsKummer_galoisAction
#print axioms germAction_mem_kummerImage

end LeanFormal.IUT.XiFPaper.S2016KummerEquivarianceActual
