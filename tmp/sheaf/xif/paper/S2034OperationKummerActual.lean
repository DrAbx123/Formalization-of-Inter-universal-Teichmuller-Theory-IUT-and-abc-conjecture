import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import tmp.sheaf.xif.paper.S1973PsiCnsActual

/-!
# S2034: the operation-level Kummer/evaluation isomorphism on the actual local
O^x / O^xmu carrier

Layer: **O** (original Theta-link / q-pilot).  Direct worker of S1978; consumers:
the S1967 reduced kappa^{x mu} audit (tmp/sheaf/xif/paper/S1967OUnitsMuActual.lean),
the S1951 reduced Kummer-evaluation square
(tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean) and the S1973
Psi_env/Psi_gau evaluation (tmp/sheaf/xif/paper/S1973PsiCnsActual.lean).

## Paper object

IUT II, Corollary 4.10, (ii) [corpus text "Inter-universal Teichmuller Theory
II.txt", lines 10355-10415]: the evaluation isomorphisms of Corollary 4.6,
(iv), (v), determine an evaluation isomorphism F^boxplus_env ~ F^boxplus_gau
of F^boxplus-prime-strips.  At the unit level the Kummer content is the
x mu-Kummer structure of IUT II, Definition 4.9, (i) [lines 10035-10098]: an
Ism-orbit of G-equivariant isomorphisms O^{x mu}(G) ~ O^{x mu}(A) of
(dual semi-)ind-topological modules, equivalently the invariant submodules
I^kappa_H(A) = Im(O^x(G)^H).  Corollary 4.10, (iv) [lines 10471-10499] states
that the unit portions of the theta and Gaussian monoids give natural
isomorphisms F^{triangleright x mu}_Delta ~ F^{triangleright x mu}_env ~
F^{triangleright x mu}_gau.  The evaluation therefore acts as the identity
on the unit portion; its non-unit (Gaussian/theta) content is the
Psi-evaluation of Proposition 4.1, (iv), formalized in S1973.

## What S1978 left open

S1978 attaches the actual local O^x carrier (Integers (AlgebraicClosure
Q_p))^x, with the actual local absolute Galois action, to the S1895 place
type as the F-prime-strip localOFieldStrip, and proves its O^{x mu}
quotient nontrivial (the unit 1 + p).  It does not construct the
operation-level Kummer/evaluation content on that carrier: its canonical
KappaOrbitUnitsActionDatum is the identity completion of Definition 4.9,
(i), with no invariant-image comparison and no relation to the S1951 square or
to S1973's evaluation.

## What this file constructs (kernel-checked, no sorry, no axiom)

Everything below lives on the actual local carrier of S1978, over the
actual local Galois product group LocalOFieldGaloisProduct (with the same
fallback indiscrete topology that S1978/S1951 use; the paper's profinite
topology remains the separate missing datum of S1967, (e)):

1. The actual O^x module and its G-action (actualOUnits,
   actualOUnitsAction, actualOUnitsMu, actualOUnitsMuAction): the actual
   integral units of the algebraic closure, acted on by the actual local
   Galois group through the actual evaluation factorization at the place.
2. The operation-level Kummer isomorphism kappa^{x mu}
   (actualKummerIso): a genuine TimesMuKummer.Isomorphism from the
   group-theoretic module O^{x mu}(G) (the actual local units with their
   actual Galois action) to the Frobenioid side O^{x mu}(A) (the strip's
   units quotient), with the Definition 4.9, (i) equivariance law and the
   invariant-image law kappa '' I_H(G) = I_H(A) proved for every open
   subgroup H (here every subgroup, by the fallback topology).  Its
   underlying equivalence is the canonical group-units transport, and it is
   not an identity completion: the module is the nontrivial actual local
   unit group, and actualKummerIso_class_ne_one proves that the class of the
   concrete nontrivial unit 1 + p is carried to a nontrivial class.
3. The operation-level evaluation isomorphism of Corollary 4.10, (ii)
   (operationEvaluationIso), built as the two-corner Ism-orbit comparison
   through the common module: the KappaOrbitUnitsActionPairDatum
   actualPairDatum has both corners on the actual local strip, and its
   layerKummer is the unit-level evaluation arrow.  Theorem
   operationEvaluationIso_eq_refl proves the paper's statement that the
   evaluation restricts to the identity on the unit portion; theorem
   operationEvaluation_orbit_has_nontrivial_representative proves that the
   Ism-orbit nevertheless contains a representative (the inversion
   invComparison) that differs from the identity on the class of 1 + p,
   and invIsometry_ne_one proves the Ism subgroup itself is nontrivial on
   the actual carrier.  This is exactly the structure that the degenerate
   S1487 carrier of S1967 could not support (its Ism is trivial there).
4. The S1951 Kummer-evaluation square on the actual local carrier
   (actualLayer, actualUnitPortion, actualKummerArrow,
   actualEvaluationArrow, actualSquare): S1951's generic three-legs
   construction instantiated on the actual local strip with the actual source
   links.  Theorems actualSquare_upper_unitLayer_eq_id,
   operationEvaluationIso_compat_square and
   actualSquare_upper_unitLayer_actualUnitCoeff_ne_one identify the square's
   upper evaluation unit layer with the S2034 operation-level evaluation iso
   and evaluate it on the nontrivial unit class.

## Exact first missing (no fake)

The paper-level Corollary 4.10, (ii) evaluation isomorphism is not
constructed.  The precise gaps, in dependency order, are:

(M1) The local-model bridge between S1973 and S1978.  S1973's evaluation
     psiEvaluation is defined on the S1962/S1966 finite-stage local model:
     the base field Base (QPlace v) (the adic completion of Q at v.1),
     its algebraic closure Closure (QPlace v), the Galois group Gv v, and
     the units PsiCnsUnits v = (IndIntegralMonoid (QPlace v))^x.  S2034's
     operation-level structure is defined on the S1978 model: Q_[v.1],
     AlgebraicClosure Q_[v.1], LocalAbsoluteGalois v.1, and
     LocalOFieldUnitsAt v = (Integers (AlgebraicClosure Q_[v.1]))^x.  The
     two models are different carriers; there is no algebraic equivalence
     between them in the tree (S1978 records the same non-identification
     between the S1949 completion-level carrier and its Q_p model).  The
     missing datum is recorded below as the structure
     PsiCnsLocalModelBridge v, with no inhabitant; the conditional theorem
     bridge_quotient_equivariant shows that a bridge would transport the
     S2034 Kummer structure to the S1973 Psi-units, and nothing weaker
     suffices, since the two unit carriers live in different types.
(M2) The F^boxplus theta/Gaussian monoid carriers of Corollary 4.6,
     (iv), (v).  The non-unit content of the evaluation (the Gaussian
     monoid, the q-pilot, the realified Frobenioids C^boxplus_env,
     C^boxplus_gau) is not constructed on the actual local carrier; S1973
     gives the actual local monoid model, but not the F^boxplus-prime-
     strips.  S2034 therefore constructs the unit portion only.
(M3) The S1895 attachment.  S1951's square lives on the four reduced
     source strips of the S1895 input, whose values are the degenerate S1487
     monoid; S1978's S1978FirstMissing (a rebased OriginalInput whose
     (1,0) core is the actual local strip) remains the exact missing object
     for connecting the actual local square of this file to the S1895 square.
     S2034's square is the actual-local-carrier square, not the S1895 one.

No sorry, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
assumption-only Nonempty gate is used.  The only conditional statements are
the bridge_* interface lemmas, whose hypothesis PsiCnsLocalModelBridge is
recorded as missing and is not used to close any unconditional result.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2034OperationKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open General

/-! ## 1. The actual local O^x module and its actual G-action -/

/-- The S1895 place type, on which the S1978 actual local strip is defined. -/
abbrev LocV : Type := PaperV

/-- The actual local Galois product group of S1978. -/
abbrev LocG : Type := LocalOFieldGaloisProduct

/-- The actual local O^x module at a place: the units of the actual integral
closure of the p-adic valuation ring.  This is the nontrivial carrier of
S1978, not the degenerate S1487 value monoid of S1967. -/
abbrev actualOUnits (v : LocV) : Type := LocalOFieldUnitsAt v

/-- The actual local Galois action on the actual O^x module, through the
actual evaluation factorization of the product group at the place. -/
noncomputable abbrev actualOUnitsAction (v : LocV) :
    LocG →* MulAut (actualOUnits v) :=
  (LocalOFieldUnitsActionAt v).comp (localOFieldFactorization v)

/-- The actual O^{x mu} quotient. -/
abbrev actualOUnitsMu (v : LocV) : Type := TimesMuQuotient (actualOUnits v)

/-- The descended action on the actual O^{x mu} quotient. -/
noncomputable abbrev actualOUnitsMuAction (v : LocV) :
    LocG →* MulAut (actualOUnitsMu v) :=
  TimesMuQuotient.action (actualOUnitsAction v)

/-- The action of the actual Galois product group on the units of the actual
local strip (the Frobenioid side O^{x mu}(A)). -/
noncomputable abbrev actualStripUnitsAction (v : LocV) :
    LocG →* MulAut ((localOFieldStrip.Mon v)ˣ) :=
  (localOFieldStrip.unitsAction v).comp (localOFieldFactorization v)

@[simp] theorem actualOUnitsMuAction_quotientMap (v : LocV) (g : LocG)
    (u : actualOUnits v) :
    actualOUnitsMuAction v g (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (actualOUnitsAction v g u) := rfl

/-- The place-indexed concrete nontrivial actual unit 1 + p. -/
noncomputable abbrev actualUnit (v : LocV) : actualOUnits v :=
  @localOFieldUnit v.1 ⟨v.prime⟩

/-- The class of 1 + p is nontrivial in the actual O^{x mu}. -/
theorem actualUnit_quotient_ne_one (v : LocV) :
    TimesMuQuotient.quotientMap (actualUnit v) ≠ 1 :=
  @localOFieldUnit_quotient_ne_one v.1 ⟨v.prime⟩

/-- The actual O^{x mu} module is nontrivial at every place. -/
theorem actualOUnitsMu_nontrivial (v : LocV) :
    (TimesMuQuotient.quotientMap (actualUnit v) : actualOUnitsMu v) ≠ 1 :=
  actualUnit_quotient_ne_one v

/-- The actual unit coefficient on the strip side: the image of `1 + p` under
the canonical identification of the actual `O^x` group with its unit group. -/
noncomputable def actualUnitCoeff (v : LocV) :
    (localOFieldStrip.Mon v)ˣ :=
  groupUnitsEquiv (actualOUnits v) (actualUnit v)

/-- The underlying local unit of the actual unit coefficient is `1 + p`. -/
theorem actualUnitCoeff_coe (v : LocV) :
    ((actualUnitCoeff v : (localOFieldStrip.Mon v)ˣ) :
        localOFieldStrip.Mon v) =
      (actualUnit v : localOFieldStrip.Mon v) := rfl

/-- The coefficient `1 + p` is not a root of unity on the strip side. -/
theorem actualUnitCoeff_not_torsion (v : LocV) :
    actualUnitCoeff v ∉ CommGroup.torsion ((localOFieldStrip.Mon v)ˣ) := by
  intro h
  have hfin : IsOfFinOrder (actualUnitCoeff v) :=
    (CommGroup.mem_torsion (actualUnitCoeff v)).mp h
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hcoe := congrArg
    (fun u : (localOFieldStrip.Mon v)ˣ => (u : localOFieldStrip.Mon v)) hpow
  have hpow' : (actualUnit v : localOFieldStrip.Mon v) ^ n = 1 := by
    change ((actualUnitCoeff v : (localOFieldStrip.Mon v)ˣ) :
      localOFieldStrip.Mon v) ^ n = 1
    simpa [actualUnitCoeff, groupUnitsEquiv, Units.val_pow_eq_pow_val] using hcoe
  exact @localOFieldUnit_not_isOfFinOrder v.1 ⟨v.prime⟩
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow'⟩)

/-- The class of the actual unit coefficient is nontrivial in the actual
`O^{x mu}` of the strip. -/
theorem actualUnitCoeff_quotient_ne_one (v : LocV) :
    TimesMuQuotient.quotientMap (actualUnitCoeff v) ≠ 1 := by
  intro h
  apply actualUnitCoeff_not_torsion v
  have hker : actualUnitCoeff v ∈ MonoidHom.ker
      (TimesMuQuotient.quotientMap (U := ((localOFieldStrip.Mon v)ˣ))) :=
    MonoidHom.mem_ker.mpr h
  simpa [TimesMuQuotient.quotientMap_ker] using hker

/-! ## 2. Two general lemmas on the torsion quotient -/

/-- A multiplicative equivalence preserves the torsion subgroup. -/
theorem mem_torsion_mapEquiv_iff {U W : Type*} [CommGroup U] [CommGroup W]
    (e : U ≃* W) (u : U) :
    e u ∈ CommGroup.torsion W ↔ u ∈ CommGroup.torsion U := by
  constructor
  · intro h
    obtain ⟨n, hn, hpow⟩ :=
      isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion (e u)).mp h)
    exact (CommGroup.mem_torsion u).mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, hn, e.injective (by rw [map_pow, hpow, map_one])⟩)
  · intro h
    obtain ⟨n, hn, hpow⟩ :=
      isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion u).mp h)
    exact (CommGroup.mem_torsion (e u)).mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, hn, by rw [← map_pow, hpow, map_one]⟩)

/-- The class of the image of a non-torsion element is nontrivial. -/
theorem quotientMap_mapEquiv_ne_one {U W : Type*} [CommGroup U] [CommGroup W]
    (e : U ≃* W) {u : U} (hu : TimesMuQuotient.quotientMap u ≠ 1) :
    TimesMuQuotient.quotientMap (e u) ≠ 1 := by
  intro h
  apply hu
  have hker : e u ∈ MonoidHom.ker
      (TimesMuQuotient.quotientMap (U := W)) :=
    MonoidHom.mem_ker.mpr h
  have htors : e u ∈ CommGroup.torsion W := by
    simpa [TimesMuQuotient.quotientMap_ker] using hker
  have hu' : u ∈ CommGroup.torsion U :=
    (mem_torsion_mapEquiv_iff e u).mp htors
  rw [← MonoidHom.mem_ker, TimesMuQuotient.quotientMap_ker]
  exact hu'

/-- A G-equivariant multiplicative equivalence of the source modules carries
the invariant submodule I^kappa_H(G) onto the invariant submodule
I^kappa_H(A) of the target: the invariant-image law of IUT II, Definition
4.9, (i), at one representative. -/
theorem quotientUnitsEquiv_image_invariantImage
    {G : Type*} [Group G] [TopologicalSpace G]
    {U W : Type*} [CommGroup U] [CommGroup W]
    {source : G →* MulAut U} {target : G →* MulAut W}
    (e : U ≃* W) (he : ∀ (g : G) (u : U), e (source g u) = target g (e u))
    (H : OpenSubgroup G) :
    quotientUnitsEquiv e ''
        (TimesMuKummer.invariantImage source H : Set (TimesMuQuotient U)) =
      (TimesMuKummer.invariantImage target H : Set (TimesMuQuotient W)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ :=
      (TimesMuKummer.mem_invariantImage_iff source H y).mp hy
    refine (TimesMuKummer.mem_invariantImage_iff target H _).mpr
      ⟨e u, ?_, ?_⟩
    · intro g
      rw [← he, hu g]
    · rw [quotientUnitsEquiv_quotientMap]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨TimesMuQuotient.quotientMap (e.symm w), ?_, ?_⟩
    · refine (TimesMuKummer.mem_invariantImage_iff source H _).mpr
        ⟨e.symm w, ?_, rfl⟩
      intro g
      apply e.injective
      rw [he, MulEquiv.apply_symm_apply, hw g]
    · rw [quotientUnitsEquiv_quotientMap, MulEquiv.apply_symm_apply]

/-! ## 3. The operation-level Kummer isomorphism kappa^{x mu} on the actual
local carrier -/

/-- The quotient-level transport along the canonical identification of a group
with its unit group: the underlying equivalence of the operation-level Kummer
isomorphism from O^{x mu}(G) to O^{x mu}(A). -/
noncomputable def kummerMuEquiv (v : LocV) :
    actualOUnitsMu v ≃* TimesMuQuotient ((localOFieldStrip.Mon v)ˣ) :=
  quotientUnitsEquiv (groupUnitsEquiv (actualOUnits v))

/-- Pointwise formula on quotient classes. -/
theorem kummerMuEquiv_quotientMap (v : LocV) (u : actualOUnits v) :
    kummerMuEquiv v (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap
        ((groupUnitsEquiv (actualOUnits v)) u : (localOFieldStrip.Mon v)ˣ) :=
  quotientUnitsEquiv_quotientMap _ u

/-- The canonical identification of the actual local `O^x` group with its unit
group intertwines the actual local Galois action with the actual strip units
action: the commutativity law that makes the Kummer transport equivariant. -/
theorem actualUnits_naturality (v : LocV) (g : LocG) (u : actualOUnits v) :
    (groupUnitsEquiv (actualOUnits v) (actualOUnitsAction v g u) :
        (localOFieldStrip.Mon v)ˣ) =
      actualStripUnitsAction v g (groupUnitsEquiv (actualOUnits v) u) := by
  change groupUnitsEquiv (LocalOFieldUnitsAt v)
      (LocalOFieldUnitsActionAt v (localOFieldFactorization v g) u) =
    (localOFieldStrip.unitsAction v (localOFieldFactorization v g))
      (groupUnitsEquiv (LocalOFieldUnitsAt v) u)
  rw [← localOFieldStrip_unitsAction_groupUnitsEquiv]

/-- **The operation-level Kummer isomorphism kappa^{x mu} on the actual local
O^x/O^{x mu} carrier.**  A G-equivariant isomorphism
O^{x mu}(G) ~> O^{x mu}(A) with the invariant-image law of IUT II,
Definition 4.9, (i), built from the actual local units, the actual local
Galois action and the actual evaluation factorization. -/
noncomputable def actualKummerIso (v : LocV) :
    TimesMuKummer.Isomorphism (actualOUnitsAction v)
      (actualStripUnitsAction v) where
  equiv := kummerMuEquiv v
  equivariant := by
    intro g x
    obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
    simp only [TimesMuQuotient.action_quotientMap, kummerMuEquiv_quotientMap]
    exact congrArg
      (TimesMuQuotient.quotientMap (U := ((localOFieldStrip.Mon v)ˣ)))
      (actualUnits_naturality v g u)
  invariantImage := by
    intro H
    change quotientUnitsEquiv (groupUnitsEquiv (actualOUnits v)) ''
        (TimesMuKummer.invariantImage (actualOUnitsAction v) H :
          Set (actualOUnitsMu v)) =
      (TimesMuKummer.invariantImage (actualStripUnitsAction v) H :
        Set (TimesMuQuotient ((localOFieldStrip.Mon v)ˣ)))
    exact quotientUnitsEquiv_image_invariantImage
      (W := ((localOFieldStrip.Mon v)ˣ))
      (groupUnitsEquiv (actualOUnits v))
      (fun g u => actualUnits_naturality v g u) H

/-- The Kummer isomorphism is equivariant, in the Definition 4.9, (i), form. -/
theorem actualKummerIso_equivariant (v : LocV) (g : LocG)
    (x : actualOUnitsMu v) :
    (actualKummerIso v).equiv (TimesMuQuotient.action (actualOUnitsAction v) g x) =
      TimesMuQuotient.action (actualStripUnitsAction v) g
        ((actualKummerIso v).equiv x) :=
  (actualKummerIso v).equivariant g x

/-- The invariant-image law kappa '' I_H(G) = I_H(A). -/
theorem actualKummerIso_invariantImage (v : LocV) (H : OpenSubgroup LocG) :
    (actualKummerIso v).equiv ''
        (TimesMuKummer.invariantImage (actualOUnitsAction v) H :
          Set (actualOUnitsMu v)) =
      (TimesMuKummer.invariantImage (actualStripUnitsAction v) H :
        Set (TimesMuQuotient ((localOFieldStrip.Mon v)ˣ))) :=
  (actualKummerIso v).invariantImage H

/-- **Nontriviality of the actual Kummer structure.**  The class of the
concrete non-torsion unit 1 + p is carried to a nontrivial class, so
actualKummerIso is not a collapse of the actual O^{x mu}. -/
theorem actualKummerIso_class_ne_one (v : LocV) :
    (actualKummerIso v).equiv
      (TimesMuQuotient.quotientMap (actualUnit v)) ≠ 1 := by
  change kummerMuEquiv v (TimesMuQuotient.quotientMap (actualUnit v)) ≠ 1
  rw [kummerMuEquiv_quotientMap]
  exact actualUnitCoeff_quotient_ne_one v

/-! ## 4. The Definition 4.9, (i), datum and the operation-level evaluation
isomorphism of Corollary 4.10, (ii) -/

/-- The x mu-Kummer datum of IUT II, Definition 4.9, (i), on the actual local
O^x strip, with the actual local units as the group-theoretic module O^x(G). -/
noncomputable def actualKappaDatum :
    KappaOrbitUnitsActionDatum LocG localOFieldStrip where
  sourceUnits := actualOUnits
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := actualOUnitsAction
  factor := localOFieldFactorization
  kappa := actualKummerIso

/-- The two-corner datum: the env and gau corners are both the actual local
O^x strip, and the common module is the actual O^x(G). -/
noncomputable def actualPairDatum :
    KappaOrbitUnitsActionPairDatum LocG localOFieldStrip localOFieldStrip where
  sourceUnits := actualOUnits
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := actualOUnitsAction
  factorUpper := localOFieldFactorization
  factorLower := localOFieldFactorization
  kappaUpper := actualKummerIso
  kappaLower := actualKummerIso

/-- **The operation-level evaluation isomorphism of IUT II, Corollary 4.10,
(ii), on the actual local O^{x mu} carrier**: the two-corner Ism-orbit
comparison carried by the common actual module O^{x mu}(G). -/
noncomputable abbrev operationEvaluationIso (v : LocV) :
    TimesMuKummer.Isomorphism (actualStripUnitsAction v)
      (actualStripUnitsAction v) :=
  actualPairDatum.layerKummer v

/-- The evaluation isomorphism is the identity on the unit portion (Corollary
4.10, (iv): the unit portions of the theta and Gaussian monoids agree). -/
theorem operationEvaluationIso_apply (v : LocV)
    (x : TimesMuQuotient ((localOFieldStrip.Mon v)ˣ)) :
    (operationEvaluationIso v).equiv x = x := by
  change ((actualKummerIso v).equiv.symm.trans (actualKummerIso v).equiv) x = x
  rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-- The operation-level evaluation isomorphism is the identity representative
of the Ism-orbit: the paper's statement that the evaluation restricts to the
identity on the unit portion. -/
theorem operationEvaluationIso_eq_refl (v : LocV) :
    operationEvaluationIso v =
      TimesMuKummer.Isomorphism.refl (actualStripUnitsAction v) := by
  apply TimesMuKummer.Isomorphism.ext
  apply MulEquiv.ext
  intro x
  rw [operationEvaluationIso_apply]
  rfl

/-! ## 5. Nontrivial Ism-orbit on the actual carrier -/

/-- Inversion as a multiplicative automorphism of a commutative group. -/
noncomputable def invMulAut (U : Type*) [CommGroup U] : MulAut U where
  toFun u := u⁻¹
  invFun u := u⁻¹
  left_inv u := inv_inv u
  right_inv u := inv_inv u
  map_mul' u v := by rw [mul_inv_rev, mul_comm]

theorem invMulAut_apply (U : Type*) [CommGroup U] (u : U) :
    invMulAut U u = u⁻¹ := rfl

/-- Inversion of the actual O^{x mu} quotient is a G-isometry of the
Definition 4.9, (i), module: it commutes with the action and preserves every
invariant submodule. -/
noncomputable def invIsometry (v : LocV) :
    TimesMuKummer.Ism (actualStripUnitsAction v) :=
  ⟨TimesMuQuotient.descendAut (invMulAut ((localOFieldStrip.Mon v)ˣ)), by
    constructor
    · intro g x
      obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
      simp only [TimesMuQuotient.action_quotientMap,
        TimesMuQuotient.descendAut_quotientMap]
      refine congrArg
        (TimesMuQuotient.quotientMap (U := ((localOFieldStrip.Mon v)ˣ))) ?_
      rw [invMulAut_apply, invMulAut_apply, map_inv]
    · intro H
      have hstable : ∀ x : TimesMuQuotient ((localOFieldStrip.Mon v)ˣ),
          x ∈ TimesMuKummer.invariantImage (actualStripUnitsAction v) H →
          TimesMuQuotient.descendAut (invMulAut ((localOFieldStrip.Mon v)ˣ)) x ∈
            TimesMuKummer.invariantImage (actualStripUnitsAction v) H := by
        intro x hx
        obtain ⟨u, hu, rfl⟩ :=
          (TimesMuKummer.mem_invariantImage_iff (actualStripUnitsAction v) H x).mp hx
        refine (TimesMuKummer.mem_invariantImage_iff
          (actualStripUnitsAction v) H _).mpr ⟨u⁻¹, ?_, ?_⟩
        · intro g
          rw [map_inv, hu g]
        · rw [TimesMuQuotient.descendAut_quotientMap, invMulAut_apply]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hstable y hy
      · intro hx
        refine ⟨TimesMuQuotient.descendAut
          (invMulAut ((localOFieldStrip.Mon v)ˣ)) x, hstable x hx, ?_⟩
        obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
        rw [TimesMuQuotient.descendAut_quotientMap,
          TimesMuQuotient.descendAut_quotientMap, invMulAut_apply, invMulAut_apply,
          inv_inv]⟩


/-- The classes of the actual unit coefficient and of its inverse are
different in O^{x mu}. -/
theorem quotientMap_inv_ne (v : LocV) :
    TimesMuQuotient.quotientMap (actualUnitCoeff v)⁻¹ ≠
      TimesMuQuotient.quotientMap (actualUnitCoeff v) := by
  intro h
  have hmul : TimesMuQuotient.quotientMap (actualUnitCoeff v) *
      TimesMuQuotient.quotientMap (actualUnitCoeff v) = 1 := by
    calc TimesMuQuotient.quotientMap (actualUnitCoeff v) *
          TimesMuQuotient.quotientMap (actualUnitCoeff v)
        = TimesMuQuotient.quotientMap (actualUnitCoeff v) *
            TimesMuQuotient.quotientMap (actualUnitCoeff v)⁻¹ := by rw [h]
      _ = TimesMuQuotient.quotientMap
            (actualUnitCoeff v * (actualUnitCoeff v)⁻¹) := by rw [map_mul]
      _ = 1 := by simp
  have hmem : actualUnitCoeff v * actualUnitCoeff v ∈
      CommGroup.torsion ((localOFieldStrip.Mon v)ˣ) := by
    have hker : actualUnitCoeff v * actualUnitCoeff v ∈
        MonoidHom.ker
          (TimesMuQuotient.quotientMap (U := (localOFieldStrip.Mon v)ˣ)) :=
      MonoidHom.mem_ker.mpr (by simpa [map_mul] using hmul)
    simpa [TimesMuQuotient.quotientMap_ker] using hker
  have hfin : IsOfFinOrder (actualUnitCoeff v * actualUnitCoeff v) :=
    (CommGroup.mem_torsion (actualUnitCoeff v * actualUnitCoeff v)).mp hmem
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  apply actualUnitCoeff_not_torsion v
  refine (CommGroup.mem_torsion (actualUnitCoeff v)).mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * n, by positivity, ?_⟩)
  rw [pow_mul]
  simpa [pow_two] using hpow

/-- **The Ism subgroup of the actual local O^{x mu} carrier is nontrivial**:
inversion is a non-identity G-isometry.  This is the structure that the
degenerate S1487 carrier of S1967 could not support. -/
theorem invIsometry_ne_one (v : LocV) :
    invIsometry v ≠ (1 : TimesMuKummer.Ism (actualStripUnitsAction v)) := by
  intro h
  have hval : (invIsometry v :
      MulAut (TimesMuQuotient ((localOFieldStrip.Mon v)ˣ))) =
      (1 : MulAut (TimesMuQuotient ((localOFieldStrip.Mon v)ˣ))) :=
    congrArg
      (fun f : TimesMuKummer.Ism (actualStripUnitsAction v) =>
        (f : MulAut (TimesMuQuotient ((localOFieldStrip.Mon v)ˣ)))) h
  have hval' : (TimesMuQuotient.descendAut
      (invMulAut ((localOFieldStrip.Mon v)ˣ))) =
      (1 : MulAut (TimesMuQuotient ((localOFieldStrip.Mon v)ˣ))) := hval
  have happly := congrArg
    (fun f : MulAut (TimesMuQuotient ((localOFieldStrip.Mon v)ˣ)) =>
      f (TimesMuQuotient.quotientMap (actualUnitCoeff v))) hval'
  rw [TimesMuQuotient.descendAut_quotientMap, invMulAut_apply] at happly
  simp only [MulAut.one_apply] at happly
  exact quotientMap_inv_ne v happly

/-- Inversion as a full Kummer isomorphism of the actual local O^{x mu}
carrier (a representative of the Ism-orbit distinct from the identity one). -/
noncomputable def invComparison (v : LocV) :
    TimesMuKummer.Isomorphism (actualStripUnitsAction v)
      (actualStripUnitsAction v) where
  equiv := TimesMuQuotient.descendAut (invMulAut ((localOFieldStrip.Mon v)ˣ))
  equivariant := (invIsometry v).property.1
  invariantImage := (invIsometry v).property.2

theorem invComparison_apply (v : LocV)
    (u : (localOFieldStrip.Mon v)ˣ) :
    (invComparison v).equiv (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap u⁻¹ := by
  change TimesMuQuotient.descendAut (invMulAut ((localOFieldStrip.Mon v)ˣ))
      (TimesMuQuotient.quotientMap u) = TimesMuQuotient.quotientMap u⁻¹
  rw [TimesMuQuotient.descendAut_quotientMap, invMulAut_apply]

/-- **The Ism-orbit of the operation-level evaluation contains a
representative that is not the identity representative**: its value at the
class of 1 + p differs from the evaluation's value there. -/
theorem operationEvaluation_orbit_has_nontrivial_representative (v : LocV) :
    ∃ κ : TimesMuKummer.Isomorphism (actualStripUnitsAction v)
        (actualStripUnitsAction v),
      κ.equiv (TimesMuQuotient.quotientMap (actualUnitCoeff v)) ≠
        (operationEvaluationIso v).equiv
          (TimesMuQuotient.quotientMap (actualUnitCoeff v)) := by
  refine ⟨invComparison v, ?_⟩
  rw [invComparison_apply, operationEvaluationIso_apply]
  exact quotientMap_inv_ne v

/-! ## 6. The S1951 Kummer-evaluation square on the actual local carrier -/

/-- S1951's strip-equivalence Kummer layer, instantiated on the actual local
strip with the actual source link (the identity strip equivalence) and the
actual evaluation factorization. -/
noncomputable def actualLayer :
    SourceTimesMuKummerLayer LocG localOFieldStrip localOFieldStrip :=
  General.layerOfFactors (FPrimeStripEquiv.refl localOFieldStrip)
    localOFieldFactorization

/-- The unit portion of the S1951 evaluation arrow on the actual local strip. -/
noncomputable def actualUnitPortion :
    SourceEvaluationUnitPortion LocG localOFieldStrip localOFieldStrip :=
  SourceEvaluationUnitPortion.ofKummerLayer actualLayer

/-- The S1951 vertical Kummer arrow on the actual local strip. -/
noncomputable def actualKummerArrow :
    SourceKummerArrow LocG localOFieldStrip localOFieldStrip :=
  sourceKummerArrowOfLayer (FPrimeStripEquiv.refl localOFieldStrip) actualLayer

/-- The S1951 evaluation arrow on the actual local strip. -/
noncomputable def actualEvaluationArrow :
    SourceEvaluationArrow LocG localOFieldStrip localOFieldStrip :=
  sourceEvaluationArrowOfUnitPortion (FPrimeStripEquiv.refl localOFieldStrip)
    actualUnitPortion

/-- **The S1951 Kummer-evaluation square on the actual local O^x carrier**,
built by the paper's conjugation instruction (three free legs plus the lower
unit portion). -/
noncomputable def actualSquare :
    SourceKummerEvaluationSquare LocG localOFieldStrip localOFieldStrip
      localOFieldStrip localOFieldStrip :=
  SourceKummerEvaluationSquare.ofThreeLegs actualEvaluationArrow actualKummerArrow
    actualKummerArrow actualUnitPortion

/-- The forced lower horizontal of the actual square is the conjugation of the
upper horizontal by the two actual Kummer representatives. -/
theorem actualSquare_lowerHorizontal_stripIso :
    actualSquare.lowerHorizontal.stripIso =
      actualSquare.leftKummer.stripIso.trans
        (actualSquare.upperHorizontal.stripIso.trans
          actualSquare.rightKummer.stripIso.symm) :=
  SourceKummerEvaluationSquare.lowerHorizontal_stripIso_eq actualSquare

/-- The two-path equality of the actual square. -/
theorem actualSquare_twoPath :
    actualSquare.domainExpression = actualSquare.codomainExpression :=
  actualSquare.domainExpression_eq_codomainExpression

/-- On the actual local strip the S1951 layer's Kummer equivalence is the
identity on quotient classes. -/
theorem actualLayer_kummer_quotientMap (v : LocV)
    (u : (localOFieldStrip.Mon v)ˣ) :
    (actualLayer.kummer v).equiv (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap u := by
  change quotientUnitsEquiv
      (Units.mapEquiv ((FPrimeStripEquiv.refl localOFieldStrip).isoMon v))
      (TimesMuQuotient.quotientMap u) = TimesMuQuotient.quotientMap u
  rw [quotientUnitsEquiv_quotientMap]
  congr 1

/-- The S1951 evaluation unit layer on the actual local strip is the identity
on O^{x mu}. -/
theorem actualSquare_upper_unitLayer_eq_id (v : LocV)
    (x : TimesMuQuotient ((localOFieldStrip.Mon v)ˣ)) :
    (actualSquare.upperHorizontal.unitPortion.unitLayer v) x = x := by
  obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
  change (actualLayer.kummer v).equiv (TimesMuQuotient.quotientMap u) =
    TimesMuQuotient.quotientMap u
  exact actualLayer_kummer_quotientMap v u

/-- The S1951 square's upper evaluation unit layer and the S2034 operation-level
evaluation isomorphism agree on the actual O^{x mu}, after the canonical
identification of the group-theoretic module with the strip's unit module. -/
theorem operationEvaluationIso_compat_square (v : LocV)
    (x : actualOUnitsMu v) :
    (actualSquare.upperHorizontal.unitPortion.unitLayer v)
        (kummerMuEquiv v x) =
      (operationEvaluationIso v).equiv (kummerMuEquiv v x) := by
  rw [actualSquare_upper_unitLayer_eq_id, operationEvaluationIso_apply]

/-- The actual square's upper unit layer evaluated on the nontrivial class of
1 + p is the class itself, and it is nontrivial. -/
theorem actualSquare_upper_unitLayer_actualUnitCoeff_ne_one (v : LocV) :
    (actualSquare.upperHorizontal.unitPortion.unitLayer v)
        (TimesMuQuotient.quotientMap (actualUnitCoeff v)) ≠ 1 := by
  rw [actualSquare_upper_unitLayer_eq_id]
  exact actualUnitCoeff_quotient_ne_one v

/-! ## 7. The exact first missing -/

/-- **The exact missing local-model comparison between S1973 and S1978.**  The
S1973 Psi-evaluation is defined on the S1962/S1966 finite-stage local model
(Base (QPlace v), Closure (QPlace v), Gv v, PsiCnsUnits v), while the
S2034 operation-level Kummer structure is defined on the S1978 Q_p-model
(Q_[v.1], AlgebraicClosure Q_[v.1], LocalAbsoluteGalois v.1,
LocalOFieldUnitsAt v).  These are different carriers and the tree contains
no algebraic equivalence between them.  The structure below is recorded, not
inhabited: constructing it is the first missing object. -/
structure PsiCnsLocalModelBridge (v : LocV) where
  /-- the comparison of the local unit modules O^x -/
  unitsEquiv : PsiCnsUnits v ≃* actualOUnits v
  /-- the comparison of the local absolute Galois groups -/
  galoisEquiv : Gv v ≃* @LocalAbsoluteGalois v.1 ⟨v.prime⟩
  /-- the comparison intertwines the two actual Galois actions -/
  unitsAction_compat : ∀ (σ : Gv v) (u : PsiCnsUnits v),
    unitsEquiv (psiCnsUnitsAction v σ u) =
      LocalOFieldUnitsActionAt v (galoisEquiv σ) (unitsEquiv u)

/-- Conditional interface: a PsiCnsLocalModelBridge would transport the S1973
Psi-unit action to the actual local action at the level of O^{x mu}.  This
is the only statement in this file that depends on the missing bridge; no
unconditional result uses it. -/
theorem bridge_quotient_equivariant (v : LocV) (B : PsiCnsLocalModelBridge v)
    (σ : Gv v) (x : TimesMuQuotient (PsiCnsUnits v)) :
    quotientUnitsEquiv B.unitsEquiv
        (TimesMuQuotient.action (psiCnsUnitsAction v) σ x) =
      TimesMuQuotient.action
        ((LocalOFieldUnitsActionAt v).comp B.galoisEquiv.toMonoidHom) σ
        (quotientUnitsEquiv B.unitsEquiv x) := by
  obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
  simp only [TimesMuQuotient.action_quotientMap, quotientUnitsEquiv_quotientMap]
  congr 1
  simpa [MonoidHom.comp_apply] using B.unitsAction_compat σ u

/-- The second missing object: S1978's rebased S1895 input.  S1951's square is
the square of the four reduced source strips of the S1895 input; the actual
local square of section 6 is the square on the actual local carrier alone.
Connecting them requires the rebased input (S1978, section 7). -/
abbrev S1895AttachmentMissing (D : S1895OIdentificationsActual.S1895PaperInput) : Type 1 :=
  S1978RebasedPaperInput D

/-! ## 8. Axiom probes -/

#print axioms actualKummerIso
#print axioms actualKummerIso_invariantImage
#print axioms actualKummerIso_class_ne_one
#print axioms actualKappaDatum
#print axioms operationEvaluationIso_eq_refl
#print axioms invIsometry
#print axioms invIsometry_ne_one
#print axioms operationEvaluation_orbit_has_nontrivial_representative
#print axioms actualSquare
#print axioms actualSquare_lowerHorizontal_stripIso
#print axioms actualSquare_twoPath
#print axioms operationEvaluationIso_compat_square
#print axioms actualSquare_upper_unitLayer_actualUnitCoeff_ne_one
#print axioms bridge_quotient_equivariant

end LeanFormal.IUT.XiFPaper.S2034OperationKummerActual
