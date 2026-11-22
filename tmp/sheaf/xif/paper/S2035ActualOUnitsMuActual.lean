import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceGaloisLogShell
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitGaloisDescent
import LeanFormal.IUT.IUTII.Kummer.TimesMuIsm
import LeanFormal.IUT.IUTII.Kummer.AlgebraicClosureKummerRoots
import Mathlib.FieldTheory.KrullTopology
set_option maxHeartbeats 4000000

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

The file constructs, at this group, the following actual data:

* OUnitsActual v = (L_v)^×, the group of units of the algebraic closure (the
  groupification of the nonzero integral monoid O^⊠_Fv), with the actual
  G_v-action OUnitsActualAction v (the honest Galois action on the algebraic
  closure, not a transported abstract action);
* OUnitsMuActual v = torsion (OUnitsActual v) with the restricted action;
* OUnitsMuQuotientActual v = TimesMuQuotient (OUnitsActual v), with the
  descended action;
* GvEquiv v : G_v ~= Gal(Q_p^alg/Q_p), unitsEquiv v : OUnitsActual v ~=
  QpUnits v, and unitsEquiv_action, which proves that unitsEquiv intertwines
  the actual action with the Q_p model action through GvEquiv.  These are
  proved from the canonical ring equivalence of algebraic closures of
  isomorphic fields (IsAlgClosure.equivOfEquiv), with explicit use of
  equivOfEquiv_algebraMap and equivOfEquiv_symm_algebraMap on both sides.

It also proves:

* Fixed points.  The fixed points of the actual G_v-action on OUnitsActual v
  are exactly the image of K_v^× (mem_fixed_iff_base).
* Fixed integral units.  The actual integral units O_v^× are identified with
  the actual Galois-fixed integral units of L_v (fixedIntegralUnitsEquiv), and
  actualOUnitsPadicEquiv identifies O_v^× with Z_p^×.

The Kummer isomorphism, the uniformizer nontriviality theorem, and the pointed
OUnitsOutput functoriality described in earlier drafts of this header are not
present in this version; this file proves the section-3 comparison together
with the fixed-point and integral-base results listed above.

## Completion carrier status (checked 2026-11-02)

This is **not** the completion-level carrier O^×/O^×μ of IUT I, §1 and IUT II,
Example 1.8, (iii), (iv).  In IUT I, §1, for F_v an algebraic closure of K_v,

  O_Fv     = ring of integers of F_v,
  O^⊠_Fv  ⊆ O_Fv = the multiplicative monoid of nonzero integers,
  O^×_Fv  ⊆ O_Fv = the multiplicative monoid of units,
  O^μ_Fv  ⊆ O^×_Fv = roots of unity,
  O^×μ_Fv = O^×_Fv / O^μ_Fv.

Thus the paper's local O^× is (Integers (Lv v))ˣ, the units of the actual
integral ring of L_v, not (Lv v)ˣ.  The carrier OUnitsActual v = (Lv v)ˣ is the
groupification of O^⊠_Fv; it contains elements of norm != 1 (e.g. a
uniformizer of K_v), which are not in (Integers (Lv v))ˣ.  Accordingly,
unitsEquiv v identifies the actual all-units group with the Q_p all-units
group, and unitsEquiv_action is a genuine equivariance statement for that
all-units action, but neither is an identification of the paper O^×/O^×μ
carrier.

## Exact first missing

The first missing datum is the actual integral-units carrier

  OUnitsIntegralActual v := (Integers (Lv v))ˣ,

together with its actual G_v-action (obtained from localGaloisUnitMap after
restricting σ : Lv v ≃ₐ[Kv v] Lv v to an automorphism over the p-adic scalar
field) and its torsion quotient TimesMuQuotient (OUnitsIntegralActual v).  In
particular, no O^×μ carrier is constructed.  The comparison with the Q_p
model also needs an integer-preserving (isometric) equivalence

  (Integers (Lv v))ˣ ≃* (Integers (AlgebraicClosure Q_p))ˣ

compatible with GvEquiv v.  The existing algClosureEquiv v is only a ring
equivalence; the file proves no theorem that it maps Integers (Lv v) to
Integers (AlgebraicClosure Q_p), so it does not induce such an equivalence.
The normalized-completion integer-preservation result available in the tree
(normalizedCompletionRingEquiv_image_integers) is only for
NormalizedCompletion (QPlace v), not for the algebraic closure.

A separate, later gap is the Aut(G_v)-action of the group-theoretic algorithm
of [AbsTopIII], Proposition 5.8, (i), recorded as

  S2035FirstMissing v := AutActionData v,

a monoid homomorphism Aut(G_v) ->* MulAut (OUnitsActual v) extending the actual
action along inner automorphisms.  It is recorded as a structure with no
inhabitant; the Zhat^×-action and the ind-topology continuity of S1975 are
further gaps.

No sorry, admit, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
Nonempty gate is used.  Axiom probes are at the end of the file.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S2035ActualOUnitsMuActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

local instance factPrime (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) :=
  ⟨v.2.2.2⟩

local instance factPrimeNatPrimes (v : FinitePrimePlace 2 7) :
    Fact (Nat.Prime (⟨v.1, v.2.2.2⟩ : Nat.Primes).val) :=
  ⟨v.2.2.2⟩

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
    LocalAbsoluteGalois v.1 where
  toFun x := (algClosureEquiv v).symm (σ ((algClosureEquiv v) x))
  invFun x := (algClosureEquiv v).symm (AlgEquiv.symm σ ((algClosureEquiv v) x))
  left_inv x := by
    simp only [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply,
      AlgEquiv.symm_apply_apply]
  right_inv x := by
    simp only [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply,
      AlgEquiv.apply_symm_apply]
  map_mul' x y := by
    simp only [map_mul]
  map_add' x y := by
    simp only [map_add]
  commutes' x := by
    have he : algClosureEquiv v (algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1]) x) =
        algebraMap (Kv v) (Lv v) (completionPadicEquiv v x) :=
      IsAlgClosure.equivOfEquiv_algebraMap (L := AlgebraicClosure ℚ_[v.1])
        (M := Lv v) (completionPadicEquiv v) x
    rw [he, σ.commutes]
    simp [algClosureEquiv]

noncomputable def galoisConjSymm (v : FinitePrimePlace 2 7)
    (τ : LocalAbsoluteGalois v.1) : Gv v where
  toFun x := (algClosureEquiv v) (τ ((algClosureEquiv v).symm x))
  invFun x := (algClosureEquiv v) (AlgEquiv.symm τ ((algClosureEquiv v).symm x))
  left_inv x := by
    simp only [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply,
      AlgEquiv.symm_apply_apply]
  right_inv x := by
    simp only [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply,
      AlgEquiv.apply_symm_apply]
  map_mul' x y := by
    simp only [map_mul]
  map_add' x y := by
    simp only [map_add]
  commutes' y := by
    have hs : (algClosureEquiv v).symm (algebraMap (Kv v) (Lv v) y) =
        algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1])
          ((completionPadicEquiv v).symm y) :=
      IsAlgClosure.equivOfEquiv_symm_algebraMap (L := AlgebraicClosure ℚ_[v.1])
        (M := Lv v) (completionPadicEquiv v) y
    rw [hs, τ.commutes]
    simp [algClosureEquiv]

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
      exact u.ne_zero (by simpa [h0] using hx.symm)
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
  apply Subtype.ext
  simpa [actualOUnitsToActual] using congrArg Units.val h

noncomputable def actualOUnitsPadicEquiv (v : FinitePrimePlace 2 7) :
    (Ov v)ˣ ≃* ℤ_[(⟨v.1, v.2.2.2⟩ : Nat.Primes)]ˣ :=
  (Units.mapEquiv (RingEquiv.cast
    (R := fun m : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ) => m.adicCompletionIntegers ℚ)
    (rationalFinitePlace_underlyingPrime v.1)).toMulEquiv).trans
    (Units.mapEquiv ((PadicInt.adicCompletionIntegersEquiv
      (R := NumberField.RingOfIntegers ℚ)
      (⟨v.1, v.2.2.2⟩ : Nat.Primes)).symm).toMulEquiv)

/-! ## 8. The pointed group-theoretic output and the exact first missing -/

structure AutActionData (v : FinitePrimePlace 2 7) where
  action : MulAut (Gv v) →* MulAut (OUnitsActual v)
  inner_compat : ∀ g : Gv v,
    action (MulAut.conj g) = OUnitsActualAction v g

abbrev S2035FirstMissing (v : FinitePrimePlace 2 7) : Type :=
  AutActionData v

/-! ## 9. Axiom probes -/

#print axioms unitsEquiv
#print axioms GvEquiv
#print axioms unitsEquiv_action
#print axioms mem_fixed_iff_base
#print axioms fixedIntegralUnitsEquiv
#print axioms actualOUnitsPadicEquiv

end LeanFormal.IUT.XiFPaper.S2035ActualOUnitsMuActual
