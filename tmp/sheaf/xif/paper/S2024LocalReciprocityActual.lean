import tmp.sheaf.xif.paper.S2017VerlagerungActual
import LeanFormal.IUT.IUTII.Frobenioid.LocalTorsionCyclotome

/-!
# S2024: (M2) local reciprocity on torsion -- reduction and exact first missing

Layer: **O** (original Theta-link / q-pilot).  Consumer: the S2017 package
(tmp/sheaf/xif/paper/S2017VerlagerungActual.lean), whose muQZComparison p
and muHatComparison p are the two remaining comparison propositions, and
through it the [AbsTopIII] Corollary 1.10 interface of S2000/S2011.

## The statement being attacked

S2011's (M2) is

  localReciprocityOnTorsion p :
  for every open subgroup U of G_v = Gal(Qbar_p / Q_p),
  torsion (Abelianization U) ~= torsion (FixedField U)^x,

i.e. the levelwise identification (H^ab)_tors = mu(L_H) of local class field
theory, where L_H = FixedField H.  The transfer compatibility refinement (the
Verlagerung K^ab -> H^ab for H <= K must become the inclusion
mu(L_K) -> mu(L_H) of the roots of unity of the two fixed fields) is the
second half of (M2), recorded in S2017's module doc.

## What this file proves (unconditional, no sorry, no axiom)

1.  fixedField_le, fixedFieldTorsionUnitsInclusion: for H <= K the
    canonical inclusion of finite fields L_K <= L_H induces canonically
    torsion (L_K)^x -> torsion (L_H)^x, with injectivity and composition
    laws (torsionUnitsMap_comp, torsionUnitsMap_val_comp_inclusion).

2.  LocalReciprocityData p: the formal (M2) datum on the tree's carriers:
    levelwise multiplicative equivalences
    torsion (Abelianization U) ~= torsion (FixedField U)^x
    together with exactly the transfer compatibility square consumed by the
    universal property of muQZ (stageHom_toStage).

3.  **Reduction of (M2) to the S2017 comparisons.**
    muQZToClosure, muQZAddEquiv, muQZComparison_of_data,
    muHatComparison_of_muQZComparison, muHatComparison_of_data:
    any LocalReciprocityData p yields
      muQZ p ~= torsion (O^tri)^x           (muQZComparison p), hence
      muHat^Z p ~= PsiCnsTorsionCyclotome p  (muHatComparison p).
    The proof assembles the levelwise data through muQZ_lift; injectivity
    uses muQZ_exists_stage (every class of the colimit is represented in a
    single stage; the index lattice of open subgroups is downward directed)
    together with injectivity of the transfer maps forced by the
    compatibility square, and surjectivity uses that every root of unity is
    fixed by an open subgroup (openStabilizer).

4.  localReciprocityOnTorsion_of_data: the S2011 statement follows from the
    data, so the data is a correct refinement of (M2) on the tree's carriers.

## The exact first missing (not assumed, not faked)

The first missing input is the **construction** of LocalReciprocityData p:

(M2a) **Levelwise local reciprocity on torsion.**  For every open U, the
      multiplicative equivalence torsion (Ab U) ~= torsion (FixedField U)^x.
      This is local class field theory on torsion.  Neither Mathlib (this
      revision, v4.32.2) nor the tree contains the local Artin/reciprocity
      map for finite extensions of Q_p, a maximal abelian extension L^ab as an
      intermediate field, or the identification Gal(L^ab/L) ~= hat(L^x).
      Generic norm maps (Algebra.norm) and profinite completions of abstract
      groups do exist in Mathlib; what is absent is the reciprocity map and
      its norm compatibility.  The closest available objects for (M2) are the
      abstract abelianization Abelianization U of Mathlib and the concrete
      fixed fields FixedField p U; no theorem relates their torsion
      subgroups.  Hence (M2a) is genuinely missing, not merely unassembled.

(M2b) **Transfer compatibility.**  For H <= K the Verlagerung
      verlagerungOpen h : Ab K -> Ab H must correspond, under the
      identifications of (M2a), to the inclusion of roots of unity
      torsion (FixedField K)^x -> torsion (FixedField H)^x.  In local class
      field theory this is the norm-compatibility of the reciprocity map
      (Ver o rec_K = rec_L o incl for L <= K).  It is a separate theorem
      about the reciprocity map, again absent.  The present file isolates it
      as the single field transfer_compat of LocalReciprocityData and proves
      that exactly this field is what the colimit's universal property
      consumes.

(M2c) **Abstract vs. profinite abelianization.**  Mathlib's Abelianization U
      is the quotient by the ordinary commutator subgroup [U,U]; the source's
      (U^ab) is the profinite (closed-commutator) abelianization
      U / closure([U,U]).  Local class field theory identifies the
      *profinite* abelianization with the profinite completion hat(L^x), and
      the torsion of hat(L^x) is mu(L).  The statement
      localReciprocityOnTorsion p is made on the abstract carrier, so its
      identification with the literal profinite source statement requires an
      extra comparison between the abstract torsion and the profinite
      torsion.  That comparison is not supplied by the tree's definitions and
      is not proved here: the tree has the abstract Abelianization, while the
      profinite carrier is not used in the S2011 statement.  This is recorded
      as a statement-level caveat rather than hidden.  LocalReciprocityData is
      stated on exactly the same abstract carrier as S2011, so the reduction
      below is a correct formal theorem about that carrier; the literal
      source statement additionally requires the profinite comparison.

The **first missing in dependency order** is therefore (M2a): the levelwise
reciprocity isomorphism for one finite local field, equivalently the local
Artin map.  Transfer compatibility (M2b) is a second, independent input; the
abstract-vs-profinite gap (M2c) is a statement-level caveat on the source
identification and is a further input required for the literal source
statement, not for the abstract-carrier reduction proved here.

Both localReciprocityOnTorsion p (S2011) and localReciprocityDataMissing p are
stated below and left unproved.  No sorry, admit, axiom, True/PUnit slot, empty
structure, arbitrary inhabitant, or assumption-only Nonempty gate is
introduced.

## Not run

Full Project build, target comparator, independent review, and the [AbsTopIII]
group-theoretic construction itself.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false

noncomputable section
open scoped DirectSum
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual

namespace LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. Torsion units of fields and of the local integral monoid -/

/-- Composition of the torsion-unit maps of two composable ring homs. -/
theorem torsionUnitsMap_comp {F E D : Type*} [Field F] [Field E] [Field D]
    (f : F →+* E) (g : E →+* D) :
    RationalCircleCyclotome.torsionUnitsMap (g.comp f) =
      (RationalCircleCyclotome.torsionUnitsMap g).comp
        (RationalCircleCyclotome.torsionUnitsMap f) := by
  ext x
  rfl

/-- Injectivity of the torsion-unit map of an injective ring hom. -/
theorem torsionUnitsMap_injective {F E : Type*} [Field F] [Field E]
    (f : F →+* E) (hf : Function.Injective f) :
    Function.Injective (RationalCircleCyclotome.torsionUnitsMap f) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply hf
  exact congrArg (fun z : CommGroup.torsion Eˣ => ((z : Eˣ) : E)) hxy

/-- The additive hom attached to a multiplicative hom, through Additive. -/
noncomputable def additiveOfMulHom {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Additive G →+ Additive H where
  toFun x := Additive.ofMul (f (Additive.toMul x))
  map_zero' := by
    change Additive.ofMul (f (Additive.toMul 0)) =
      Additive.ofMul (Additive.toMul (0 : Additive H))
    rw [show Additive.toMul (0 : Additive G) = 1 from rfl]
    rw [show Additive.toMul (0 : Additive H) = 1 from rfl]
    rw [map_one]
  map_add' x y := by
    change Additive.ofMul (f (Additive.toMul (x + y))) =
      Additive.ofMul (f (Additive.toMul x)) +
        Additive.ofMul (f (Additive.toMul y))
    rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl]
    rw [map_mul]
    rfl

@[simp] theorem additiveOfMulHom_apply {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : Additive G) :
    additiveOfMulHom f x = Additive.ofMul (f (Additive.toMul x)) := rfl

@[simp] theorem additive_toMul_ofMul {G : Type*} [Group G] (x : G) :
    Additive.toMul (Additive.ofMul x) = x := rfl

@[simp] theorem additive_ofMul_toMul {G : Type*} [AddGroup G] (x : Additive G) :
    Additive.ofMul (Additive.toMul x) = x := rfl

/-- Injectivity of additiveOfMulHom. -/
theorem additiveOfMulHom_injective {G H : Type*} [Group G] [Group H]
    {f : G →* H} (hf : Function.Injective f) :
    Function.Injective (additiveOfMulHom f) := by
  intro x y hxy
  have h1 : f (Additive.toMul x) = f (Additive.toMul y) := by
    simpa using congrArg Additive.toMul hxy
  exact Additive.toMul.injective (hf h1)

/-! ## 2. The fixed-field torsion-unit inclusions -/

/-- The fixed field is antitone in the open subgroup. -/
theorem fixedField_le {H K : Index p} (h : H ≤ K) :
    LocalIntegralUnitKummerInjectivity.FixedField p K ≤
      LocalIntegralUnitKummerInjectivity.FixedField p H :=
  IntermediateField.fixedField_antitone h

/-- For H <= K the inclusion of fixed fields L_K <= L_H induces the
canonical map on torsion units. -/
noncomputable def fixedFieldTorsionUnitsInclusion {H K : Index p} (h : H ≤ K) :
    CommGroup.torsion (LocalIntegralUnitKummerInjectivity.FixedField p K)ˣ →*
      CommGroup.torsion (LocalIntegralUnitKummerInjectivity.FixedField p H)ˣ :=
  RationalCircleCyclotome.torsionUnitsMap
    (IntermediateField.inclusion (fixedField_le p h)).toRingHom

/-- The fixed-field torsion-unit inclusion is injective. -/
theorem fixedFieldTorsionUnitsInclusion_injective {H K : Index p} (h : H ≤ K) :
    Function.Injective (fixedFieldTorsionUnitsInclusion p h) :=
  torsionUnitsMap_injective _ (IntermediateField.inclusion_injective _)

/-- The fixed-field inclusion is compatible with the ambient embedding into
the algebraic closure: val_H o incl_{K <= H} = val_K on torsion units. -/
theorem torsionUnitsMap_val_comp_inclusion {H K : Index p} (h : H ≤ K) :
    (RationalCircleCyclotome.torsionUnitsMap
        (IntermediateField.val
          (LocalIntegralUnitKummerInjectivity.FixedField p H)).toRingHom).comp
        (fixedFieldTorsionUnitsInclusion p h) =
      RationalCircleCyclotome.torsionUnitsMap
        (IntermediateField.val
          (LocalIntegralUnitKummerInjectivity.FixedField p K)).toRingHom := by
  rw [fixedFieldTorsionUnitsInclusion, ← torsionUnitsMap_comp]
  congr 1

/-! ## 3. The formal (M2) datum -/

/-- **(M2) on the tree's carriers.**  Levelwise local reciprocity on torsion
together with its compatibility with the Verlagerung.  This structure is the
precise missing input: it is not inhabited in this file, and no theorem here
produces one from the existing carriers.  See the module doc for the
decomposition (M2a)-(M2c) and for the abstract-vs-profinite caveat. -/
structure LocalReciprocityData : Type where
  /-- Levelwise local reciprocity on torsion: (U^ab)_tors = mu(FixedField U). -/
  equiv : ∀ U : Index p,
    CommGroup.torsion (Abelianization U) ≃*
      CommGroup.torsion (LocalIntegralUnitKummerInjectivity.FixedField p U)ˣ
  /-- The Verlagerung Ab K -> Ab H (H <= K) corresponds to the inclusion of
  the roots of unity mu(FixedField K) -> mu(FixedField H). -/
  transfer_compat : ∀ {H K : Index p} (h : H ≤ K)
      (v : CommGroup.torsion (Abelianization K)),
    equiv H (torsionMap (verlagerungOpen p h) v) =
      fixedFieldTorsionUnitsInclusion p h (equiv K v)

/-- The S2011 statement is the levelwise half of (M2). -/
theorem localReciprocityOnTorsion_of_data (data : LocalReciprocityData p) :
    localReciprocityOnTorsion p :=
  fun U => ⟨data.equiv U⟩

/-! ## 4. The stage maps and their transfer compatibility -/

/-- The additive group of torsion units of the algebraic closure. -/
abbrev ClosureTorsion : Type :=
  Additive (CommGroup.torsion (AlgebraicClosure ℚ_[p])ˣ)

/-- The levelwise map (U^ab)_tors -> mu(Qbar_p) obtained from a local
reciprocity datum. -/
noncomputable def stageHom (data : LocalReciprocityData p) (H : Index p) :
    Stage p H →+ ClosureTorsion p :=
  (additiveOfMulHom
    (RationalCircleCyclotome.torsionUnitsMap
      (IntermediateField.val
        (LocalIntegralUnitKummerInjectivity.FixedField p H)).toRingHom)).comp
    (data.equiv H).toAdditive.toAddMonoidHom

@[simp] theorem stageHom_apply (data : LocalReciprocityData p) (H : Index p)
    (v : Stage p H) :
    stageHom p data H v =
      Additive.ofMul
        (RationalCircleCyclotome.torsionUnitsMap
          (IntermediateField.val
            (LocalIntegralUnitKummerInjectivity.FixedField p H)).toRingHom
          (data.equiv H (Additive.toMul v))) := rfl

/-- **Transfer compatibility of the stage maps.**  This is exactly the square
of LocalReciprocityData.transfer_compat, transported to the colimit's stage
maps. -/
theorem stageHom_toStage (data : LocalReciprocityData p) {H K : Index p}
    (h : H ≤ K) (v : Stage p K) :
    stageHom p data H (toStage p h v) = stageHom p data K v := by
  rw [stageHom_apply, stageHom_apply, toStage]
  simp only [additive_toMul_ofMul]
  rw [data.transfer_compat h]
  rw [← MonoidHom.comp_apply, torsionUnitsMap_val_comp_inclusion p h]

/-- Injectivity of each stage map. -/
theorem stageHom_injective (data : LocalReciprocityData p) (H : Index p) :
    Function.Injective (stageHom p data H) := by
  intro v w hvw
  have hinj : Function.Injective
      (RationalCircleCyclotome.torsionUnitsMap
        (IntermediateField.val
          (LocalIntegralUnitKummerInjectivity.FixedField p H)).toRingHom) :=
    torsionUnitsMap_injective _
      (fun a b hab => Subtype.ext hab)
  have h1 : (data.equiv H).toAdditive v = (data.equiv H).toAdditive w :=
    additiveOfMulHom_injective hinj hvw
  exact (data.equiv H).toAdditive.injective h1

/-- Under (M2) the Verlagerung on torsion is injective: it is the inclusion of
the roots of unity of the two fixed fields. -/
theorem toStage_injective_of_data (data : LocalReciprocityData p) {H K : Index p}
    (h : H ≤ K) : Function.Injective (toStage p h) := by
  intro v w hvw
  have h1 : stageHom p data K v = stageHom p data K w := by
    rw [← stageHom_toStage p data h v, ← stageHom_toStage p data h w, hvw]
  exact stageHom_injective p data K h1

/-! ## 5. Every class of the colimit lives in a single stage -/

/-- **Single-stage representation.**  Every element of the direct limit
mu_{Q/Z}(G_v) is the image of an element of one stage.  The index lattice of
open subgroups is downward directed (finite intersections), which lets the
finitely many summands of a class be pushed to a common lower stage. -/
theorem muQZ_exists_stage (x : muQZ p) :
    ∃ (L : Index p) (w : Stage p L), x = muQZof p L w := by
  classical
  refine QuotientAddGroup.induction_on x ?_
  intro z
  let P : (⨁ H : Index p, Stage p H) → Prop := fun z =>
    ∃ (L : Index p) (w : Stage p L),
      (QuotientAddGroup.mk' (muQZRel p)) z = muQZof p L w
  change P z
  induction z using DirectSum.induction_on with
  | zero =>
      refine ⟨⊤, 0, ?_⟩
      change (QuotientAddGroup.mk' (muQZRel p)) (0 : ⨁ H : Index p, Stage p H) =
        muQZof p ⊤ 0
      rw [map_zero, map_zero]
  | of H v =>
      refine ⟨H, v, ?_⟩
      change (QuotientAddGroup.mk' (muQZRel p))
          ((DirectSum.of (Stage p) H) v) = muQZof p H v
      rw [muQZof]
      rfl
  | add x y hx hy =>
      obtain ⟨Lx, wx, hxw⟩ := hx
      obtain ⟨Ly, wy, hyw⟩ := hy
      refine ⟨Lx ⊓ Ly,
        toStage p inf_le_left wx + toStage p inf_le_right wy, ?_⟩
      rw [map_add, hxw, hyw]
      rw [← muQZof_transfer p inf_le_left wx,
        ← muQZof_transfer p inf_le_right wy]
      rw [← map_add]

/-! ## 6. The comparison muQZ ~= torsion (O^tri)^x -/

/-- The colimit map assembled from a local reciprocity datum. -/
noncomputable def muQZToClosure (data : LocalReciprocityData p) :
    muQZ p →+ ClosureTorsion p :=
  muQZ_lift p (ClosureTorsion p) (stageHom p data)
    (fun {H K : Index p} h v => stageHom_toStage p data h v)

/-- Computation rule for the assembled map. -/
theorem muQZToClosure_of (data : LocalReciprocityData p) (H : Index p)
    (v : Stage p H) :
    muQZToClosure p data (muQZof p H v) = stageHom p data H v :=
  muQZ_lift_of p (ClosureTorsion p) (stageHom p data)
    (fun {H K : Index p} h v => stageHom_toStage p data h v) H v

/-- The assembled map is injective. -/
theorem muQZToClosure_injective (data : LocalReciprocityData p) :
    Function.Injective (muQZToClosure p data) := by
  intro x y hxy
  obtain ⟨Lx, wx, rfl⟩ := muQZ_exists_stage p x
  obtain ⟨Ly, wy, rfl⟩ := muQZ_exists_stage p y
  let L : Index p := Lx ⊓ Ly
  have hx : muQZof p Lx wx = muQZof p L (toStage p inf_le_left wx) :=
    (muQZof_transfer p inf_le_left wx).symm
  have hy : muQZof p Ly wy = muQZof p L (toStage p inf_le_right wy) :=
    (muQZof_transfer p inf_le_right wy).symm
  rw [hx, hy] at hxy
  rw [muQZToClosure_of, muQZToClosure_of] at hxy
  have h := stageHom_injective p data L hxy
  rw [hx, hy, h]

/-- The assembled map is surjective: every root of unity is fixed by an open
subgroup, hence lies in the fixed field of that subgroup. -/
theorem muQZToClosure_surjective (data : LocalReciprocityData p) :
    Function.Surjective (muQZToClosure p data) := by
  intro y
  classical
  let u : CommGroup.torsion (AlgebraicClosure ℚ_[p])ˣ := Additive.toMul y
  let a : CommGroup.torsion (LocalIntegralMonoid p)ˣ :=
    (LocalIntegralMonoid.torsionEquivAlgebraicClosureTorsion p).symm u
  have ha : LocalIntegralMonoid.torsionEquivAlgebraicClosureTorsion p a = u :=
    (LocalIntegralMonoid.torsionEquivAlgebraicClosureTorsion p).apply_symm_apply u
  let aUnit : (LocalIntegralMonoid p)ˣ := a
  have hu : (u : (AlgebraicClosure ℚ_[p])ˣ) =
      LocalIntegralMonoid.unitEvaluation p aUnit := by
    rw [← ha]
    rfl
  let U : Index p := LocalIntegralMonoid.openStabilizer p (aUnit : LocalIntegralMonoid p)
  have hfixed : ∀ g : U,
      LocalIntegralMonoid.galoisAction p (g : LocalAbsoluteGalois p)
        (aUnit : LocalIntegralMonoid p) = (aUnit : LocalIntegralMonoid p) :=
    fun g => LocalIntegralMonoid.openStabilizer_fixed p _ g
  have hmem : ((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]) ∈
      LocalIntegralUnitKummerInjectivity.FixedField p U := by
    change ((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]) ∈
      IntermediateField.fixedField U.toSubgroup
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have hunit : localGaloisUnitsAction p g (u : (AlgebraicClosure ℚ_[p])ˣ) =
        (u : (AlgebraicClosure ℚ_[p])ˣ) := by
      rw [hu, ← LocalIntegralMonoid.unitEvaluation_equivariant]
      congr 1
      apply Units.ext
      exact hfixed ⟨g, hg⟩
    exact congrArg Units.val hunit
  obtain ⟨n, hn, hupow⟩ := isOfFinOrder_iff_pow_eq_one.mp
    ((CommGroup.mem_torsion (u : (AlgebraicClosure ℚ_[p])ˣ)).mp u.property)
  let xfield : LocalIntegralUnitKummerInjectivity.FixedField p U :=
    ⟨((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]), hmem⟩
  have hxfield : xfield ≠ 0 := by
    intro h
    have hzero : ((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]) = 0 :=
      congrArg Subtype.val h
    exact (u : (AlgebraicClosure ℚ_[p])ˣ).ne_zero hzero
  let w0 : (LocalIntegralUnitKummerInjectivity.FixedField p U)ˣ :=
    Units.mk0 xfield hxfield
  have hw0val : ((w0 : LocalIntegralUnitKummerInjectivity.FixedField p U) :
      AlgebraicClosure ℚ_[p]) =
      ((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]) := rfl
  have hmapw : Units.map
      (IntermediateField.val
        (LocalIntegralUnitKummerInjectivity.FixedField p U)).toRingHom.toMonoidHom w0 =
      (u : (AlgebraicClosure ℚ_[p])ˣ) := by
    apply Units.ext
    rfl
  have hw0pow : w0 ^ n = 1 := by
    have hinj : Function.Injective
        (Units.map (IntermediateField.val
          (LocalIntegralUnitKummerInjectivity.FixedField p U)).toRingHom.toMonoidHom) :=
      Units.map_injective (fun a b hab => Subtype.ext hab)
    apply hinj
    calc
      Units.map (IntermediateField.val
          (LocalIntegralUnitKummerInjectivity.FixedField p U)).toRingHom.toMonoidHom
          (w0 ^ n) =
          (Units.map (IntermediateField.val
            (LocalIntegralUnitKummerInjectivity.FixedField p U)).toRingHom.toMonoidHom
            w0) ^ n := map_pow _ _ _
      _ = (u : (AlgebraicClosure ℚ_[p])ˣ) ^ n := by rw [hmapw]
      _ = 1 := hupow
      _ = Units.map (IntermediateField.val
            (LocalIntegralUnitKummerInjectivity.FixedField p U)).toRingHom.toMonoidHom 1 :=
          (map_one _).symm
  let w : CommGroup.torsion
      (LocalIntegralUnitKummerInjectivity.FixedField p U)ˣ :=
    ⟨w0, (CommGroup.mem_torsion w0).mpr
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hw0pow⟩)⟩
  have hmap : RationalCircleCyclotome.torsionUnitsMap
      (IntermediateField.val
        (LocalIntegralUnitKummerInjectivity.FixedField p U)).toRingHom w = u := by
    apply Subtype.ext
    apply Units.ext
    rfl
  let v : CommGroup.torsion (Abelianization U) := (data.equiv U).symm w
  refine ⟨muQZof p U (Additive.ofMul v), ?_⟩
  rw [muQZToClosure_of, stageHom_apply]
  change Additive.ofMul
    (RationalCircleCyclotome.torsionUnitsMap
      (IntermediateField.val
        (LocalIntegralUnitKummerInjectivity.FixedField p U)).toRingHom
      (data.equiv U (Additive.toMul (Additive.ofMul v)))) = y
  rw [additive_toMul_ofMul]
  have hev : data.equiv U v = w := (data.equiv U).apply_symm_apply w
  rw [hev, hmap]
  rfl

/-- The multiplicative equivalence muQZ ~= torsion (O^tri)^x under a local
reciprocity datum. -/
noncomputable def muQZAddEquiv (data : LocalReciprocityData p) :
    muQZ p ≃+ ClosureTorsion p :=
  AddEquiv.ofBijective (muQZToClosure p data)
    ⟨muQZToClosure_injective p data, muQZToClosure_surjective p data⟩

/-- **M2 implies S2017's muQZComparison.** -/
theorem muQZComparison_of_data (data : LocalReciprocityData p) :
    muQZComparison p :=
  ⟨(muQZAddEquiv p data).trans
    (LocalIntegralMonoid.torsionEquivAlgebraicClosureTorsion p).toAdditive.symm⟩

/-! ## 6b. The rational-circle form of the comparison -/

/-- Under (M2) the group-theoretic cyclotome is the rational circle Q/Z, as in
[AbsTopIII], Corollary 1.10, (a). -/
theorem muQZ_addEquiv_addCircle_of_data (data : LocalReciprocityData p) :
    Nonempty (muQZ p ≃+ AddCircle (1 : ℚ)) := by
  refine ⟨(muQZAddEquiv p data).trans ?_⟩
  exact ((LocalIntegralMonoid.torsionEquivAlgebraicClosureTorsion p).symm.trans
    (LocalIntegralMonoid.torsionCyclotomicEquiv p)).toAdditive

/-- The content of muQZComparison is exactly that the group-theoretic
cyclotome is the rational circle. -/
theorem muQZComparison_iff_rationalCircle :
    muQZComparison p ↔ Nonempty (muQZ p ≃+ AddCircle (1 : ℚ)) := by
  constructor
  · rintro ⟨e⟩
    refine ⟨e.trans ?_⟩
    exact (LocalIntegralMonoid.torsionCyclotomicEquiv p).toAdditive
  · rintro ⟨e⟩
    refine ⟨e.trans ?_⟩
    exact ((LocalIntegralMonoid.torsionCyclotomicEquiv p).toAdditive).symm

/-! ## 7. Functoriality of the Kummer cyclotome -/

/-- Post-composition with a multiplicative equivalence of coefficients. -/
noncomputable def kummerCyclotomeCongr {B C : Type*} [CommGroup B] [CommGroup C]
    (e : B ≃* C) : KummerCyclotome B ≃* KummerCyclotome C where
  toFun f := e.toMonoidHom.comp f
  invFun f := e.symm.toMonoidHom.comp f
  left_inv f := by
    ext q
    simp
  right_inv f := by
    ext q
    simp
  map_mul' f g := by
    ext q
    simp

/-- The canonical equivalence Multiplicative (Additive X) ~= X. -/
noncomputable def multiplicativeAdditiveMulEquiv (X : Type*) [Group X] :
    Multiplicative (Additive X) ≃* X where
  toFun x := Additive.toMul (Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (Additive.ofMul x)
  left_inv x := by
    rfl
  right_inv x := by
    rfl
  map_mul' x y := by
    rfl

/-- **muQZComparison implies muHatComparison.** -/
theorem muHatComparison_of_muQZComparison (h : muQZComparison p) :
    muHatComparison p := by
  obtain ⟨e⟩ := h
  refine ⟨kummerCyclotomeCongr ?_⟩
  exact e.toMultiplicative.trans (multiplicativeAdditiveMulEquiv _)

/-- **M2 implies S2017's muHatComparison.** -/
theorem muHatComparison_of_data (data : LocalReciprocityData p) :
    muHatComparison p :=
  muHatComparison_of_muQZComparison p (muQZComparison_of_data p data)

/-! ## 8. The exact missing declarations (stated, not assumed) -/

/-- The missing (M2) datum: levelwise local reciprocity on torsion together
with transfer compatibility.  This is the precise first missing input; it is
not proved and no inhabitant is fabricated. -/
def localReciprocityDataMissing : Prop :=
  Nonempty (LocalReciprocityData p)

/-- The missing datum in particular supplies S2017's muQZComparison. -/
theorem muQZComparison_of_dataMissing (h : localReciprocityDataMissing p) :
    muQZComparison p := by
  obtain ⟨data⟩ := h
  exact muQZComparison_of_data p data

/-- The missing datum in particular supplies S2017's muHatComparison. -/
theorem muHatComparison_of_dataMissing (h : localReciprocityDataMissing p) :
    muHatComparison p := by
  obtain ⟨data⟩ := h
  exact muHatComparison_of_data p data

/-- S2011's (M2), recalled verbatim as the abstract-carrier statement.
(S2017 exports the same proposition under the name localReciprocityMissing.) -/
abbrev localReciprocityOnTorsionMissing : Prop := localReciprocityOnTorsion p

/-- The levelwise half of (M2) alone (without transfer compatibility); this is
the (M2a) input isolated in the module doc. -/
def localReciprocityLevelwiseMissing : Prop :=
  ∀ U : Index p,
    Nonempty (CommGroup.torsion (Abelianization U) ≃*
      CommGroup.torsion (LocalIntegralUnitKummerInjectivity.FixedField p U)ˣ)

/-- The missing datum in particular supplies the levelwise half (M2a). -/
theorem localReciprocityLevelwiseMissing_of_dataMissing
    (h : localReciprocityDataMissing p) : localReciprocityLevelwiseMissing p := by
  obtain ⟨data⟩ := h
  exact fun U => ⟨data.equiv U⟩

/-- The first missing input at a single level: local reciprocity on torsion
for one open subgroup U, i.e. the local Artin map on torsion for the finite
extension FixedField U / Q_p. -/
def levelwiseLocalReciprocity (U : Index p) : Prop :=
  Nonempty (CommGroup.torsion (Abelianization U) ≃*
    CommGroup.torsion (LocalIntegralUnitKummerInjectivity.FixedField p U)ˣ)

theorem localReciprocityLevelwiseMissing_iff :
    localReciprocityLevelwiseMissing p ↔
      ∀ U : Index p, levelwiseLocalReciprocity p U :=
  Iff.rfl

theorem localReciprocityLevelwiseMissing_eq :
    localReciprocityLevelwiseMissing p ↔ localReciprocityOnTorsion p :=
  Iff.rfl

/-! ## 9. Axiom probes -/

#print axioms torsionUnitsMap_comp
#print axioms torsionUnitsMap_injective
#print axioms additiveOfMulHom
#print axioms fixedFieldTorsionUnitsInclusion
#print axioms fixedFieldTorsionUnitsInclusion_injective
#print axioms torsionUnitsMap_val_comp_inclusion
#print axioms localReciprocityOnTorsion_of_data
#print axioms stageHom
#print axioms stageHom_toStage
#print axioms stageHom_injective
#print axioms toStage_injective_of_data
#print axioms muQZ_exists_stage
#print axioms muQZToClosure
#print axioms muQZToClosure_of
#print axioms muQZToClosure_injective
#print axioms muQZToClosure_surjective
#print axioms muQZAddEquiv
#print axioms muQZComparison_of_data
#print axioms muQZ_addEquiv_addCircle_of_data
#print axioms muQZComparison_iff_rationalCircle
#print axioms kummerCyclotomeCongr
#print axioms multiplicativeAdditiveMulEquiv
#print axioms muHatComparison_of_muQZComparison
#print axioms muHatComparison_of_data
#print axioms localReciprocityLevelwiseMissing_of_dataMissing
#print axioms muQZComparison_of_dataMissing
#print axioms muHatComparison_of_dataMissing

end LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
