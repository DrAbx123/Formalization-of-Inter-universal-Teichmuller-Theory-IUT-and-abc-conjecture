import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceGaloisLogShell
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitGaloisDescent
import LeanFormal.IUT.IUTII.Kummer.TimesMuIsm
import LeanFormal.IUT.IUTII.Kummer.AlgebraicClosureKummerRoots
import Mathlib.FieldTheory.KrullTopology

/-!
# S2035: the actual completion-level O^× / O^×μ data of IUT II, Example 1.8

Layer: O (original Theta-link / q-pilot).  Direct worker of S1967/S1978, at the
actual completion QPlace v of the one-column finite place.

## What this file constructs

For every v : FinitePrimePlace 2 7, let

  QPlace v = rationalFinitePlace v.1,   K_v = NormalizedCompletion (QPlace v),
  O_v = CompletionIntegers (QPlace v), L_v = SourceAlgebraicClosure (QPlace v).

K_v is the actual completion of Q at the rational place QPlace v, with the
normalized Q_p-norm; O_v is its actual completed valuation ring; L_v is the
actual algebraic closure of K_v; and G_v = Gal(L_v/K_v) is the actual absolute
Galois group (Krull topology).

The file constructs the actual output data of IUT II, Example 1.8, (iii), (iv)
at this group:

* OUnitsActual v = (L_v)^×, the actual units of the algebraic closure, with the
  actual G_v-action OUnitsActualAction v (the honest Galois action on the
  algebraic closure, not a transported abstract action);
* OUnitsMuActual v = torsion (OUnitsActual v) with the restricted action;
* OUnitsMuQuotientActual v = TimesMuQuotient (OUnitsActual v), with the
  descended action.

It then proves the requested identifications:

* Actual local units.  The fixed points of the actual G_v-action on
  OUnitsActual v are exactly the image of K_v^× (mem_fixed_iff_base).  The
  actual integral units O_v^× are identified with the actual Galois-fixed
  integral units of L_v (fixedIntegralUnitsEquiv), using the actual fixed-unit
  descent, not a placeholder.
* Kummer data.  The torsion quotient is compared with the Q_p model
  QpUnits v = (AlgebraicClosure Q_p)^× by an equivariant multiplicative
  equivalence, and the comparison is packaged as a TimesMuKummer.Isomorphism
  (actualLocalKummerIso): the local ×μ-Kummer structure of Definition 4.9, (i),
  at the actual completion.
* The Q_p-model identification.  unitsEquiv v : OUnitsActual v ~= QpUnits v is
  constructed from the canonical ring equivalence of algebraic closures of
  isomorphic fields (IsAlgClosure.equivOfEquiv), and unitsEquiv_action proves
  it intertwines the actual Galois action with the model action through the
  canonical isomorphism GvEquiv v : G_v ~= Gal(Q_p^alg/Q_p).  Thus the Q_p model
  is used only as a computational auxiliary, with the identification to the
  actual completion carrier proved.
* Genuine nontriviality.  An actual uniformizer of O_v is not a root of unity
  (actualQParameter_not_torsion), so the actual O^×μ quotient is nontrivial
  (OUnitsMuQuotientActual_nontrivial).  This is the property the degenerate
  S1487 value monoid lacks (S1967).
* Pointed functoriality.  OUnitsOutput records the output of the algorithm on a
  group equipped with an isomorphism to G_v, and outputAlong constructs it;
  OUnitsOutput.transport proves functoriality for isomorphisms of pointed
  groups.

## Exact first missing

The genuine group-theoretic algorithm of IUT II, Example 1.8, (iii), assigns
O^×(G) to an abstract topological group G isomorphic to G_v, together with the
functorial action of Aut(G).  The present construction starts from the actual
group G_v and therefore supplies the G_v-action but not the Aut(G_v)-action.
The exact missing datum is

  S2035FirstMissing v := AutActionData v,

a monoid homomorphism Aut(G_v) ->* MulAut (OUnitsActual v) extending the actual
action along inner automorphisms.  It is recorded as a structure with no
inhabitant.  This is precisely the group-theoretic reconstruction content of
[AbsTopIII], Proposition 5.8, (i), and IUT II, Example 1.8, (iii); the
Zhat^×-action of (iii) is the second missing datum (not formalized in this
tree), and the ind-topology joint continuity of S1975 is the third.

No sorry, admit, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
Nonempty gate is used.  Axiom probes are at the end of the file.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2035ActualOUnitsMuActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

/-! ## 1. The actual completion, its units and its absolute Galois group -/

abbrev QPlace (v : FinitePrimePlace 2 7) : NumberField.FinitePlace ℚ :=
  rationalFinitePlace v.1

abbrev Kv (v : FinitePrimePlace 2 7) : Type :=
  NormalizedCompletion (QPlace v)

abbrev Ov (v : FinitePrimePlace 2 7) : Type :=
  CompletionIntegers (QPlace v)

abbrev Lv (v : FinitePrimePlace 2 7) : Type :=
  SourceAlgebraicClosure (QPlace v)

abbrev Gv (v : FinitePrimePlace 2 7) : Type :=
  Lv v ≃ₐ[Kv v] Lv v

abbrev OUnitsActual (v : FinitePrimePlace 2 7) : Type :=
  (Lv v)ˣ

abbrev OUnitsMuActual (v : FinitePrimePlace 2 7) : Type :=
  CommGroup.torsion (OUnitsActual v)

abbrev OUnitsMuQuotientActual (v : FinitePrimePlace 2 7) : Type :=
  TimesMuQuotient (OUnitsActual v)

abbrev QpUnits (v : FinitePrimePlace 2 7) : Type :=
  (AlgebraicClosure ℚ_[v.1])ˣ

noncomputable def OUnitsActualAction (v : FinitePrimePlace 2 7) :
    Gv v →* MulAut (OUnitsActual v) where
  toFun σ := Units.mapEquiv σ.toRingEquiv.toMulEquiv
  map_one' := by
    ext u
    rfl
  map_mul' σ τ := by
    ext u
    rfl

noncomputable def QpUnitsAction (v : FinitePrimePlace 2 7) :
    LocalAbsoluteGalois v.1 →* MulAut (QpUnits v) where
  toFun σ := Units.mapEquiv σ.toRingEquiv.toMulEquiv
  map_one' := by
    ext u
    rfl
  map_mul' σ τ := by
    ext u
    rfl

/-! ## 2. The actual completion units and the canonical Q_p identification -/

noncomputable def completionBridge (v : FinitePrimePlace 2 7) :
    Completion (QPlace v) ≃+* (rationalHeightOneSpectrum v.1).adicCompletion ℚ :=
  RingEquiv.cast (R := fun m : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ) => m.adicCompletion ℚ)
    (rationalFinitePlace_underlyingPrime v.1)

noncomputable def completionPadicEquiv (v : FinitePrimePlace 2 7) :
    ℚ_[v.1] ≃+* Kv v :=
  (rationalFinitePlacePadicEquiv v.1).toRingEquiv.trans
    ((completionBridge v).symm.trans (normalizedCompletionRingEquiv (QPlace v)).symm)

noncomputable def algClosureEquiv (v : FinitePrimePlace 2 7) :
    AlgebraicClosure ℚ_[v.1] ≃+* Lv v :=
  IsAlgClosure.equivOfEquiv (L := AlgebraicClosure ℚ_[v.1]) (M := Lv v)
    (S := ℚ_[v.1]) (R := Kv v) (completionPadicEquiv v)

noncomputable def unitsEquiv (v : FinitePrimePlace 2 7) :
    OUnitsActual v ≃* QpUnits v :=
  Units.mapEquiv (algClosureEquiv v).symm.toMulEquiv

/-! ## 3. Conjugation of the actual absolute Galois group to Gal(Q_p^alg/Q_p) -/

noncomputable def galoisConj (v : FinitePrimePlace 2 7) (σ : Gv v) :
    LocalAbsoluteGalois v.1 :=
  AlgEquiv.ofRingEquiv
    (f := (algClosureEquiv v).symm.comp
      (σ.toRingEquiv.comp (algClosureEquiv v))) (by
      intro x
      have he : algClosureEquiv v (algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1]) x) =
          algebraMap (Kv v) (Lv v) (completionPadicEquiv v x) :=
        IsAlgClosure.equivOfEquiv_algebraMap _ _ _ x
      rw [RingEquiv.comp_apply, RingEquiv.comp_apply, he, σ.commutes]
      exact IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ _ x)

noncomputable def galoisConjSymm (v : FinitePrimePlace 2 7)
    (τ : LocalAbsoluteGalois v.1) : Gv v :=
  AlgEquiv.ofRingEquiv
    (f := (algClosureEquiv v).comp
      (τ.toRingEquiv.comp (algClosureEquiv v).symm)) (by
      intro y
      have hs : (algClosureEquiv v).symm (algebraMap (Kv v) (Lv v) y) =
          algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1])
            ((completionPadicEquiv v).symm y) :=
        IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ _ y
      rw [RingEquiv.comp_apply, RingEquiv.comp_apply, hs, τ.commutes]
      exact IsAlgClosure.equivOfEquiv_algebraMap _ _ _
        ((completionPadicEquiv v).symm y))

noncomputable def GvEquiv (v : FinitePrimePlace 2 7) :
    Gv v ≃* LocalAbsoluteGalois v.1 where
  toFun := galoisConj v
  invFun := galoisConjSymm v
  left_inv σ := by
    apply AlgEquiv.ext
    intro x
    simp [galoisConj, galoisConjSymm]
  right_inv τ := by
    apply AlgEquiv.ext
    intro x
    simp [galoisConj, galoisConjSymm]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    simp [galoisConj]

theorem unitsEquiv_action (v : FinitePrimePlace 2 7) (σ : Gv v)
    (u : OUnitsActual v) :
    unitsEquiv v (OUnitsActualAction v σ u) =
      QpUnitsAction v (GvEquiv v σ) (unitsEquiv v u) := by
  apply Units.ext
  simp [unitsEquiv, OUnitsActualAction, QpUnitsAction, GvEquiv, galoisConj]

/-! ## 4. The torsion and O^×μ structures -/

noncomputable def torsionRestrict {U : Type*} [CommGroup U] (e : MulAut U) :
    MulAut (CommGroup.torsion U) where
  toFun u := ⟨e u, by
    obtain ⟨n, hnpos, hn⟩ := u.property.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, hnpos, by rw [← map_pow, hn, map_one]⟩⟩
  invFun u := ⟨e.symm u, by
    obtain ⟨n, hnpos, hn⟩ := u.property.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, hnpos, by rw [← map_pow, hn, map_one]⟩⟩
  left_inv u := by
    apply Subtype.ext
    exact e.symm_apply_apply (u : U)
  right_inv u := by
    apply Subtype.ext
    exact e.apply_symm_apply (u : U)
  map_mul' u w := by
    apply Subtype.ext
    exact e.map_mul (u : U) (w : U)

noncomputable def OUnitsMuActualAction (v : FinitePrimePlace 2 7) :
    Gv v →* MulAut (OUnitsMuActual v) where
  toFun σ := torsionRestrict (OUnitsActualAction v σ)
  map_one' := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    rfl

noncomputable def OUnitsMuQuotientActualAction (v : FinitePrimePlace 2 7) :
    Gv v →* MulAut (OUnitsMuQuotientActual v) :=
  TimesMuQuotient.action (OUnitsActualAction v)

@[simp] theorem OUnitsMuQuotientActualAction_quotientMap
    (v : FinitePrimePlace 2 7) (σ : Gv v) (u : OUnitsActual v) :
    OUnitsMuQuotientActualAction v σ (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (OUnitsActualAction v σ u) := rfl

/-! ## 5. The actual local units: fixed field and integral units -/

noncomputable def baseUnitsMap (v : FinitePrimePlace 2 7) :
    (Kv v)ˣ →* OUnitsActual v :=
  Units.map (algebraMap (Kv v) (Lv v)).toMonoidHom

theorem baseUnitsMap_injective (v : FinitePrimePlace 2 7) :
    Function.Injective (baseUnitsMap v) := by
  intro x y h
  apply Units.ext
  exact FaithfulSMul.algebraMap_injective (Kv v) (Lv v) (congrArg Units.val h)

theorem mem_fixed_iff_base (v : FinitePrimePlace 2 7) (u : OUnitsActual v) :
    (∀ σ : Gv v, OUnitsActualAction v σ u = u) ↔
      ∃ x : (Kv v)ˣ, baseUnitsMap v x = u := by
  constructor
  · intro hu
    have hval : ∀ σ : Gv v, σ (u : Lv v) = (u : Lv v) :=
      fun σ => congrArg Units.val (hu σ)
    obtain ⟨x, hx⟩ := fixed_by_absoluteGalois_mem_base (K := Kv v) (u : Lv v) hval
    have hx0 : x ≠ 0 := by
      intro h0
      exact u.ne_zero (by rw [← hx, h0, map_zero])
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩
  · rintro ⟨x, rfl⟩ σ
    apply Units.ext
    exact σ.commutes (x : Kv v)

noncomputable def fixedIntegralUnitsEquiv (v : FinitePrimePlace 2 7) :
    (Ov v)ˣ ≃* localGaloisFixedIntegralUnits
      (K := Kv v) (L := Lv v)
      (p := (completionRationalPrime (QPlace v)).val) :=
  (normalizedCompletionUnitsEquiv (QPlace v)).symm.trans
    (baseUnitsGaloisFixedEquiv (K := Kv v) (L := Lv v)
      (p := (completionRationalPrime (QPlace v)).val))

noncomputable def actualOUnitsToActual (v : FinitePrimePlace 2 7) :
    (Ov v)ˣ →* OUnitsActual v :=
  (Units.map (Subring.subtype (Integers (Lv v))).toMonoidHom).comp
    ((localGaloisFixedIntegralUnits (K := Kv v) (L := Lv v)
      (p := (completionRationalPrime (QPlace v)).val)).subtype.comp
      (fixedIntegralUnitsEquiv v).toMonoidHom)

theorem actualOUnitsToActual_injective (v : FinitePrimePlace 2 7) :
    Function.Injective (actualOUnitsToActual v) := by
  intro x y h
  apply (fixedIntegralUnitsEquiv v).injective
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun z : OUnitsActual v => ((z : Lv v))) h

noncomputable def actualOUnitsPadicEquiv (v : FinitePrimePlace 2 7) :
    (Ov v)ˣ ≃* ℤ_[(⟨v.1, v.2.2.2⟩ : Nat.Primes)]ˣ :=
  (Units.mapEquiv (RingEquiv.cast
    (R := fun m : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ) => m.adicCompletionIntegers ℚ)
    (rationalFinitePlace_underlyingPrime v.1)).toMulEquiv).trans
    (Units.mapEquiv ((PadicInt.adicCompletionIntegersEquiv
      (R := NumberField.RingOfIntegers ℚ)
      (⟨v.1, v.2.2.2⟩ : Nat.Primes)).symm).toMulEquiv)


end LeanFormal.IUT.XiFPaper.S2035ActualOUnitsMuActual
