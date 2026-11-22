import tmp.sheaf.xif.paper.S2000CohomologicalPsiCnsActual
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# S2006: the Kummer kernel of the actual Psi_cns lies in the integral units

Layer: O (original Theta-link / q-pilot).  Consumer: the S2000 package
(tmp/sheaf/xif/paper/S2000CohomologicalPsiCnsActual.lean) and, through it, the
S1973 PsiCns model.

## Result

"PsiCnsKummerKernelInUnits p" is proved for the actual local field: every
element of the Grothendieck group Qbar_p^times whose Kummer class in
"PsiCnsCohomology p = lim_J H^1(J, PsiCnsCyclotome p)" is trivial is already a
unit of the nonzero integral monoid O^tri, i.e. lies in O_C^times.

## Proof

1.  Fixed field as a local field.  For an open subgroup U of
    G_v = Gal(Qbar_p/Q_p) the fixed field
    "LocalIntegralUnitKummerInjectivity.FixedField p U" is a finite extension of
    Q_p, hence an actual nonarchimedean local field.  The norm is the
    restriction of the p-adic spectral norm on the algebraic closure
    (Mathlib's PadicAlgCl normed field structure); local compactness comes from
    finite dimensionality over the complete locally compact Q_p, and the
    valuative topology / discreteness come from the norm valuation.
2.  Fixed roots from equality of Kummer classes.  If the Kummer classes of two
    nonzero integral elements a, b agree, then on a common open subgroup U the
    two canonical root-ratio cocycles differ by an explicit integral-unit
    coboundary.  Adjusting the compatible roots by the cochain produces, for
    every n > 0, a genuine element of Qbar_p^times fixed by U whose n-th power
    is b / a (see "exists_fixed_ratio_root").
3.  Kummer rigidity in the finite fixed field.  The element b / a is therefore
    infinitely divisible in the local field L fixed by U, and its n-th roots lie
    in L.  The local-field Kummer rigidity
    ("LocalFieldKummerRigidity.fieldUnit_eq_one_of_roots", proved for actual
    nonarchimedean local fields) then yields b / a = 1.
4.  Consequently x = of a / of b = 1 is the image of the unit 1.

No sorry, axiom, True/PUnit slot, empty type, arbitrary inhabitant, or
assumption-only gate is used.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open Iut
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open scoped NNReal

namespace LeanFormal.IUT.XiFPaper.S2006KummerKernelActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. The fixed field is an actual nonarchimedean local field -/

variable (U : OpenSubgroup (LocalAbsoluteGalois p))

noncomputable instance fixedFieldFiniteDimensional : FiniteDimensional ℚ_[p]
    (LocalIntegralUnitKummerInjectivity.FixedField p U) :=
  LocalIntegralUnitKummerInjectivity.fixedField_finiteDimensional p U

noncomputable instance fixedFieldCompleteSpace : CompleteSpace
    (LocalIntegralUnitKummerInjectivity.FixedField p U) :=
  FiniteDimensional.complete ℚ_[p] _

noncomputable instance fixedFieldLocallyCompact : LocallyCompactSpace
    (LocalIntegralUnitKummerInjectivity.FixedField p U) :=
  LocallyCompactSpace.of_finiteDimensional_of_complete ℚ_[p] _

noncomputable instance fixedFieldValuativeRel : ValuativeRel
    (LocalIntegralUnitKummerInjectivity.FixedField p U) :=
  ValuativeRel.ofValuation
    (NormedField.valuation (K := LocalIntegralUnitKummerInjectivity.FixedField p U) :
      Valuation (LocalIntegralUnitKummerInjectivity.FixedField p U) NNReal)

noncomputable instance fixedFieldValuationCompatible :
    (NormedField.valuation (K := LocalIntegralUnitKummerInjectivity.FixedField p U) :
      Valuation (LocalIntegralUnitKummerInjectivity.FixedField p U) NNReal).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable instance fixedFieldIsValuativeTopology : IsValuativeTopology
    (LocalIntegralUnitKummerInjectivity.FixedField p U) :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (NormedField.valuation (K := LocalIntegralUnitKummerInjectivity.FixedField p U) :
      Valuation (LocalIntegralUnitKummerInjectivity.FixedField p U) NNReal) (by
    intro s
    exact @Valued.is_topological_valuation
      (LocalIntegralUnitKummerInjectivity.FixedField p U) inferInstance NNReal inferInstance
      (NormedField.toValued (K := LocalIntegralUnitKummerInjectivity.FixedField p U)) s)

noncomputable instance fixedFieldValuativeNontrivial :
    ValuativeRel.IsNontrivial (LocalIntegralUnitKummerInjectivity.FixedField p U) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (NormedField.valuation (K := LocalIntegralUnitKummerInjectivity.FixedField p U))).mpr
    inferInstance

noncomputable instance fixedFieldIsNonarchimedeanLocalField :
    IsNonarchimedeanLocalField
      (LocalIntegralUnitKummerInjectivity.FixedField p U) where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

theorem fixedField_eq_one_of_roots
    (value : (LocalIntegralUnitKummerInjectivity.FixedField p U)ˣ)
    (roots : LocalFieldKummerRigidity.HasAllPositiveRoots value) :
    value = 1 :=
  LocalFieldKummerRigidity.fieldUnit_eq_one_of_roots
    (LocalIntegralUnitKummerInjectivity.FixedField p U) value roots

/-- If the actual Kummer classes of two nonzero integral elements agree, then on
a common open subgroup all root ratios differ by an integral-unit coboundary, and
the adjusted roots give, in every positive degree, a fixed element of
Qbar_p^times whose power is b / a. -/
theorem exists_fixed_ratio_root (a b : Otri p)
    (hclass : PsiCnsKummer p a = PsiCnsKummer p b) :
    ∃ U : OpenSubgroup (LocalAbsoluteGalois p),
      (∀ g : U, (monoAnalytic p).action p (g : LocalAbsoluteGalois p) a = a) ∧
      (∀ g : U, (monoAnalytic p).action p (g : LocalAbsoluteGalois p) b = b) ∧
      (∀ n : ℕ, 0 < n → ∃ Q : LocalGroupification p,
        (∀ g : U,
          (monoAnalytic p).groupificationAction p (g : LocalAbsoluteGalois p) Q = Q) ∧
        Q ^ n = Algebra.GrothendieckGroup.of b / Algebra.GrothendieckGroup.of a) := by
  classical
  let pair := monoAnalytic p
  let ra := canonicalIntegralKummerRootRealization p pair a
  let rb := canonicalIntegralKummerRootRealization p pair b
  have hgerm : ra.germ = rb.germ := hclass
  obtain ⟨U, hUa, hUb, cochain, hcochain⟩ := Quotient.exact hgerm
  refine ⟨U, ?_, ?_, ?_⟩
  · intro g
    exact ra.fixed ⟨(g : LocalAbsoluteGalois p), hUa g.2⟩
  · intro g
    exact rb.fixed ⟨(g : LocalAbsoluteGalois p), hUb g.2⟩
  · intro n hn
    let q : ℚ := (n : ℚ)⁻¹
    let circle : Multiplicative (AddCircle (1 : ℚ)) :=
      Multiplicative.ofAdd (q : AddCircle (1 : ℚ))
    let d : (Otri p)ˣ := cochain circle
    let eG : LocalGroupification p := unitGrothendieckHom p d
    let Aroot : LocalGroupification p := (ra.rootSystem.roots q).toMul
    let Broot : LocalGroupification p := (rb.rootSystem.roots q).toMul
    let Q : LocalGroupification p := (Broot / Aroot) / eG
    have hq : n • q = (1 : ℚ) := by
      dsimp [q]
      rw [nsmul_eq_mul]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')
    have hApow : Aroot ^ n = Algebra.GrothendieckGroup.of a := by
      have root_power := congrArg Additive.toMul (ra.rootSystem.roots.map_nsmul n q)
      change (ra.rootSystem.roots (n • q)).toMul =
        (ra.rootSystem.roots q).toMul ^ n at root_power
      rw [hq, ra.rootSystem.root_one] at root_power
      exact root_power.symm
    have hBpow : Broot ^ n = Algebra.GrothendieckGroup.of b := by
      have root_power := congrArg Additive.toMul (rb.rootSystem.roots.map_nsmul n q)
      change (rb.rootSystem.roots (n • q)).toMul =
        (rb.rootSystem.roots q).toMul ^ n at root_power
      rw [hq, rb.rootSystem.root_one] at root_power
      exact root_power.symm
    have hcircle : circle ^ n = 1 := by
      apply Multiplicative.toAdd.injective
      change n • (q : AddCircle (1 : ℚ)) = 0
      change ((n • q : ℚ) : AddCircle (1 : ℚ)) = 0
      rw [hq]
      exact AddCircle.coe_period (p := (1 : ℚ))
    have hdpow : d ^ n = 1 := by
      show cochain circle ^ n = 1
      rw [← map_pow, hcircle, map_one]
    have hepow : eG ^ n = 1 := by
      show unitGrothendieckHom p d ^ n = 1
      rw [← map_pow, hdpow, map_one]
    have hfixed : ∀ g : U,
        pair.groupificationAction p (g : pair.actingGroup) Q = Q := by
      intro g
      have hvalAg : ra.representative.valueOn hUa g circle =
          ra.ratioUnit ⟨(g : pair.actingGroup), hUa g.2⟩ q := by
        dsimp only [circle, q]
        rfl
      have hvalBg : rb.representative.valueOn hUb g circle =
          rb.ratioUnit ⟨(g : pair.actingGroup), hUb g.2⟩ q := by
        dsimp only [circle, q]
        rfl
      have hact :
          (KummerCyclotome.continuousAction
            (pair.discreteIntegralUnitAction p)).act (g : pair.actingGroup) cochain circle =
          Units.map (pair.action p (g : pair.actingGroup)).toMonoidHom d := rfl
      have hunit : rb.ratioUnit ⟨(g : pair.actingGroup), hUb g.2⟩ q
          = d⁻¹ * ra.ratioUnit ⟨(g : pair.actingGroup), hUa g.2⟩ q
            * Units.map (pair.action p (g : pair.actingGroup)).toMonoidHom d := by
        have hpoint := congrArg
          (fun f : KummerCyclotome (Otri p)ˣ => f circle) (hcochain g)
        simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at hpoint
        rw [hvalAg, hvalBg, hact] at hpoint
        exact hpoint
      have hspecA := ra.ratio_spec (⟨(g : pair.actingGroup), hUa g.2⟩) q
      have hspecB := rb.ratio_spec (⟨(g : pair.actingGroup), hUb g.2⟩) q
      have hmap : pair.groupificationAction p (g : pair.actingGroup) Broot / Broot
          = eG⁻¹ * (pair.groupificationAction p (g : pair.actingGroup) Aroot / Aroot)
              * pair.groupificationAction p (g : pair.actingGroup) eG := by
        have h := congrArg (unitGrothendieckHom p) hunit
        simp only [map_mul, map_inv] at h
        rw [← LocalMLFModelTMPair.unitGrothendieckHom_action] at h
        rw [hspecB, hspecA] at h
        exact h
      have hB : pair.groupificationAction p (g : pair.actingGroup) Broot
          = (eG⁻¹ * (pair.groupificationAction p (g : pair.actingGroup) Aroot / Aroot)
              * pair.groupificationAction p (g : pair.actingGroup) eG) * Broot := by
        rw [← hmap]
        exact (div_mul_cancel _ _).symm
      have hkey : pair.groupificationAction p (g : pair.actingGroup) (Broot / Aroot)
          = (Broot / Aroot)
            * (eG⁻¹ * pair.groupificationAction p (g : pair.actingGroup) eG) := by
        rw [map_div, hB]
        apply Additive.ofMul.injective
        simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
        abel
      show pair.groupificationAction p (g : pair.actingGroup) ((Broot / Aroot) / eG)
          = (Broot / Aroot) / eG
      rw [map_div, hkey]
      apply Additive.ofMul.injective
      simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
      abel
    have hQpow : Q ^ n = Algebra.GrothendieckGroup.of b / Algebra.GrothendieckGroup.of a := by
      show ((Broot / Aroot) / eG) ^ n = _
      rw [div_pow, div_pow, hBpow, hApow, hepow, div_one]
    exact ⟨Q, hfixed, hQpow⟩

/-! ## 3. Field-level assembly -/

/-- A unit of the algebraic closure fixed by an open subgroup is an actual unit
of the fixed field, with the same underlying field element. -/
theorem fixedField_unit_of_fixed (U : OpenSubgroup (LocalAbsoluteGalois p))
    (w : (AlgebraicClosure ℚ_[p])ˣ)
    (hw : ∀ σ : LocalAbsoluteGalois p, σ ∈ U → localGaloisUnitsAction p σ w = w) :
    ∃ wL : (LocalIntegralUnitKummerInjectivity.FixedField p U)ˣ,
      ((wL : LocalIntegralUnitKummerInjectivity.FixedField p U) :
        AlgebraicClosure ℚ_[p]) = (w : AlgebraicClosure ℚ_[p]) := by
  classical
  have hmem : (w : AlgebraicClosure ℚ_[p]) ∈
      LocalIntegralUnitKummerInjectivity.FixedField p U := by
    change (w : AlgebraicClosure ℚ_[p]) ∈ IntermediateField.fixedField U.toSubgroup
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact congrArg Units.val (hw σ hσ)
  refine ⟨Units.mk0 ⟨(w : AlgebraicClosure ℚ_[p]), hmem⟩ (by
    intro h
    exact w.ne_zero (congrArg Subtype.val h)), ?_⟩
  rfl

/-- The image in the algebraic closure of a fixed groupification element is
fixed by the same open subgroup. -/
theorem groupificationEquiv_fixed
    (Q : LocalGroupification p) (U : OpenSubgroup (LocalAbsoluteGalois p))
    (hQ : ∀ g : U,
      (monoAnalytic p).groupificationAction p (g : LocalAbsoluteGalois p) Q = Q) :
    ∀ σ : LocalAbsoluteGalois p, σ ∈ U →
      localGaloisUnitsAction p σ
        (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p Q) =
      LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p Q := by
  intro σ hσ
  have h := (monoAnalytic p).groupificationEquivAlgebraicClosureUnits_action p
    ((⟨σ, hσ⟩ : U) : LocalAbsoluteGalois p) Q
  rw [hQ ⟨σ, hσ⟩, LocalMLFModelTMPair.monoAnalytic_augmentation_apply] at h
  exact h.symm

/-! ## 4. The main theorem: the Kummer kernel lies in the units -/

/-- **The exact first missing statement of S2000 is proved.**  Every element of
the actual Grothendieck group Qbar_p^times with trivial Kummer germ is already a
unit of the nonzero integral monoid. -/
theorem PsiCnsKummerKernelInUnits_holds :
    PsiCnsKummerKernelInUnits p := by
  classical
  intro x hx
  let f := Localization.monoidOf (⊤ : Submonoid (Otri p))
  let s := f.sec x
  have hxsplit : x * Algebra.GrothendieckGroup.of (s.2 : Otri p) =
      Algebra.GrothendieckGroup.of (s.1 : Otri p) := by
    have h := f.sec_spec x
    have h' : x * (Localization.monoidOf (⊤ : Submonoid (Otri p))).toMonoidHom
          (s.2 : Otri p) =
        (Localization.monoidOf (⊤ : Submonoid (Otri p))).toMonoidHom (s.1 : Otri p) := h
    simpa only [Algebra.GrothendieckGroup.of] using h'
  have hclass : PsiCnsKummer p (s.1 : Otri p) = PsiCnsKummer p (s.2 : Otri p) := by
    have hquot : PsiCnsKummer p (s.1 : Otri p) / PsiCnsKummer p (s.2 : Otri p) = 1 := by
      have h := hx
      rw [PsiCnsKummerGroupification, Algebra.GrothendieckGroup.lift_apply] at h
      exact h
    exact div_eq_one.mp hquot
  obtain ⟨U, _hUa, _hUb, hroots⟩ :=
    exists_fixed_ratio_root p (s.1 : Otri p) (s.2 : Otri p) hclass
  obtain ⟨Q1, hQ1fix, hQ1val⟩ := hroots 1 one_pos
  let ζ : (AlgebraicClosure ℚ_[p])ˣ :=
    LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p Q1
  have hζfix : ∀ σ : LocalAbsoluteGalois p, σ ∈ U →
      localGaloisUnitsAction p σ ζ = ζ :=
    groupificationEquiv_fixed p Q1 U hQ1fix
  obtain ⟨valueL, hvalueL⟩ := fixedField_unit_of_fixed p U ζ hζfix
  have hrootsL : LocalFieldKummerRigidity.HasAllPositiveRoots valueL := by
    intro n hn
    obtain ⟨Qn, hQnfix, hQnval⟩ := hroots n hn
    let ξ : (AlgebraicClosure ℚ_[p])ˣ :=
      LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p Qn
    have hξfix : ∀ σ : LocalAbsoluteGalois p, σ ∈ U →
        localGaloisUnitsAction p σ ξ = ξ :=
      groupificationEquiv_fixed p Qn U hQnfix
    obtain ⟨rootL, hrootL⟩ := fixedField_unit_of_fixed p U ξ hξfix
    have hpow : ξ ^ n = ζ := by
      have hQ : Qn ^ n = Q1 := by
        rw [hQnval, ← hQ1val, pow_one]
      calc ξ ^ n =
            LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p (Qn ^ n) := by
            rw [map_pow]
        _ = LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p Q1 := by
            rw [hQ]
        _ = ζ := rfl
    refine ⟨rootL, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    apply Subtype.ext
    push_cast
    rw [hrootL, hvalueL]
    exact congrArg Units.val hpow
  have hvalue_one : valueL = 1 :=
    fixedField_eq_one_of_roots p U valueL hrootsL
  have hζ : ζ = 1 := by
    apply Units.ext
    have hcongr := congrArg
      (fun u : (LocalIntegralUnitKummerInjectivity.FixedField p U)ˣ =>
        ((u : LocalIntegralUnitKummerInjectivity.FixedField p U) :
          AlgebraicClosure ℚ_[p])) hvalue_one
    have hcongr' : ((valueL : LocalIntegralUnitKummerInjectivity.FixedField p U) :
        AlgebraicClosure ℚ_[p]) = 1 := by
      simpa using hcongr
    exact hvalueL.symm.trans hcongr'
  have hQ1 : Q1 = 1 := by
    apply (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p).injective
    show LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p Q1 =
      LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p 1
    rw [map_one]
    exact hζ
  have hdiv : Algebra.GrothendieckGroup.of (s.2 : Otri p) /
      Algebra.GrothendieckGroup.of (s.1 : Otri p) = 1 := by
    rw [← hQ1val, hQ1, one_pow]
  have hof : Algebra.GrothendieckGroup.of (s.2 : Otri p) =
      Algebra.GrothendieckGroup.of (s.1 : Otri p) :=
    div_eq_one.mp hdiv
  have hs : (s.2 : Otri p) = (s.1 : Otri p) := by
    have h := congrArg (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p) hof
    have h' : LocalIntegralMonoid.toAlgebraicClosureUnits p (s.2 : Otri p) =
        LocalIntegralMonoid.toAlgebraicClosureUnits p (s.1 : Otri p) := by
      rw [← LocalIntegralMonoid.groupificationToAlgebraicClosureUnits_of,
        ← LocalIntegralMonoid.groupificationToAlgebraicClosureUnits_of]
      exact h
    have h2 := congrArg Units.val h'
    apply Subtype.ext
    apply Subtype.ext
    exact h2
  have hx1 : x = 1 := by
    have h' : x * Algebra.GrothendieckGroup.of (s.2 : Otri p) =
        Algebra.GrothendieckGroup.of (s.2 : Otri p) := by
      rw [hxsplit, hs]
    exact mul_right_cancel (b := Algebra.GrothendieckGroup.of (s.2 : Otri p)) (by
      rw [one_mul]
      exact h')
  exact ⟨1, by rw [map_one]; exact hx1.symm⟩

/-- **Full injectivity of the actual Kummer map on O^tri.** -/
theorem PsiCnsKummer_injective : Function.Injective (PsiCnsKummer p) :=
  PsiCnsKummer_injective_of_kernelInUnits p (PsiCnsKummerKernelInUnits_holds p)

/-- **The actual Kummer image is multiplicatively identified with the actual
nonzero integral monoid O^tri.** -/
theorem PsiCnsKummerImage_equiv :
    Nonempty (PsiCnsKummerImage p ≃* PsiCnsModel p) :=
  PsiCnsKummerImage_equiv_of_kernelInUnits p (PsiCnsKummerKernelInUnits_holds p)

/-! ## 5. Axiom probes -/

#print axioms fixedFieldIsNonarchimedeanLocalField
#print axioms fixedField_eq_one_of_roots
#print axioms exists_fixed_ratio_root
#print axioms fixedField_unit_of_fixed
#print axioms PsiCnsKummerKernelInUnits_holds
#print axioms PsiCnsKummer_injective
#print axioms PsiCnsKummerImage_equiv

end LeanFormal.IUT.XiFPaper.S2006KummerKernelActual
