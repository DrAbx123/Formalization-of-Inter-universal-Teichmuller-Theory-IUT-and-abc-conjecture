import tmp.sheaf.xif.paper.S2430TorsionDescentSubagentActual
import tmp.sheaf.xif.paper.S2024LocalReciprocityActual

/-!
# S2442: continuity of the honest MuQZ MulAut action

Layer: O (Theta-link / q-pilot).  This file is an independent target; it
does not import the unfinished S2431MuQZMulAutSubagentActual.lean and it
does not import S2432MuQZMulAutDoneActual.lean.

## What is constructed

* S2442MuQZEnd: the additive endomorphism of muQZ p attached to
  g : Gv p, with computation rule S2442MuQZEnd_muQZof.
* S2442MuQZAction : Gv p ->* MulAut (Multiplicative (muQZ p)), the honest
  monoid hom g |-> A_(g^-1), with value formula and compatibility
  S2442MuQZAction_compat.
* S2442_action_fixed: if h in H for an open subgroup H and
  x = muQZof p H v, then h fixes x.  The point is that conjugation by
  h in H is an inner automorphism of H, hence is trivial on
  Abelianization H and on its torsion.
* S2442ActionJointContinuous_discrete: the joint action map
  Gv p x muQZ p -> muQZ p is continuous when muQZ p carries the discrete
  topology used in S2159.  Continuity does not require the source Gv p
  to be discrete: every orbit is locally constant because every x lies in
  a stage muQZof p H v and the open subgroup H fixes x.

## Source topology

Gv p is LocalAbsoluteGalois p = Gal(AlgebraicClosure Q_p / Q_p), and its
topology instance is Mathlib's Krull topology
(Mathlib.FieldTheory.KrullTopology), not a discrete topology.  This file
does not assume DiscreteTopology (Gv p); S2442SourceDiscrete below only
records that proposition so that the assumption is visible and is not
smuggled in.  The only DiscreteTopology instance for a Galois group in
Mathlib is for finite-dimensional extensions, which the algebraic closure is
not.

## Exact first missing

The tree declares only the discrete topology bottom on muQZ p (S2159).  The
paper's joint continuity for a non-discrete/profinite topology on muQZ p
is recorded as the precise proposition S2442ActionJointContinuous p T
(parameterised by T); it is assumed nowhere.  For T = bottom it is proved
unconditionally below (S2442ActionJointContinuous_discrete).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2442ContinuitySubagentActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2159MuQZActionActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2317SubgroupOfApplyActual
open LeanFormal.IUT.XiFPaper.S2371HnatExplicitActual
open LeanFormal.IUT.XiFPaper.S2430TorsionDescentSubagentActual

open scoped Pointwise

universe u

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. Transfer compatibility and the conjugation permutation -/

/-- Transfer compatibility, reused from the fully proved S2430 result. -/
theorem S2442_transferCompatible : S2179TransferCompatible (p := p) :=
  S2430_transferCompatible p

/-- Conjugating twice composes the open subgroups: conj_g (conj_h H) is
conj_(h*g) H. -/
theorem S2442ConjIndex_comp (g h : Gv p) (H : Index p) :
    S2169ConjIndex p g (S2169ConjIndex p h H) = S2169ConjIndex p (h * g) H := by
  apply OpenSubgroup.ext
  intro x
  simp only [S2169ConjIndex, OpenSubgroup.mem_comap]
  change MulAut.conj h (MulAut.conj g x) ∈ H ↔ MulAut.conj (h * g) x ∈ H
  simp only [MulAut.conj_apply]
  rw [show h * (g * x * g⁻¹) * h⁻¹ = h * g * x * (h * g)⁻¹ by group]

/-- Conjugation by 1 is the identity on open subgroups. -/
theorem S2442ConjIndex_one (H : Index p) :
    S2169ConjIndex p 1 H = H := by
  apply OpenSubgroup.ext
  intro x
  simp only [S2169ConjIndex, OpenSubgroup.mem_comap]
  change MulAut.conj (1 : Gv p) x ∈ H ↔ x ∈ H
  simp only [MulAut.conj_apply, inv_one, one_mul, mul_one]

/-- Conjugation of an open subgroup by one of its own elements is the
identity.  This is the key source-side fact behind continuity: the
stabiliser of a stage generator contains the corresponding open subgroup. -/
theorem S2442ConjIndex_self (g : Gv p) (H : Index p) (hg : g ∈ H) :
    S2169ConjIndex p g H = H := by
  apply OpenSubgroup.ext
  intro x
  simp only [S2169ConjIndex, OpenSubgroup.mem_comap]
  change MulAut.conj g x ∈ H ↔ x ∈ H
  rw [MulAut.conj_apply]
  constructor
  · intro hx
    have h : g⁻¹ * (g * x * g⁻¹) * g ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg
    have hEq : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    simpa [hEq] using h
  · intro hx
    exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)

/-- muQZof is invariant under an equality of open subgroups. -/
theorem S2442_muQZof_cast {H H' : Index p} (e : H = H') (v : Stage p H) :
    muQZof p H v = muQZof p H' (e ▸ v) := by
  cases e
  rfl

/-! ## 2. The additive endomorphism attached to g -/

/-- The levelwise family defining the endomorphism of muQZ p attached to
g : Gv p. -/
noncomputable def S2442MuQZEndFamily (g : Gv p) :
    ∀ H : Index p, Stage p H →+ muQZ p :=
  fun H =>
    (muQZof p (S2169ConjIndex p g H)).comp
      (S2179StageConj p g H).toAddMonoidHom

/-- The compatibility needed for muQZ_lift, from transfer compatibility. -/
theorem S2442MuQZEndFamily_compat (g : Gv p) :
    ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      S2442MuQZEndFamily p g H (toStage p h v) =
        S2442MuQZEndFamily p g K v := by
  intro H K h v
  obtain ⟨h', hEq⟩ := S2442_transferCompatible (p := p) g H K h v
  change muQZof p (S2169ConjIndex p g H)
      (S2179StageConj p g H (toStage p h v)) =
    muQZof p (S2169ConjIndex p g K) (S2179StageConj p g K v)
  rw [hEq, muQZof_transfer (p := p) (H := S2169ConjIndex p g H)
    (K := S2169ConjIndex p g K) h']

/-- The additive endomorphism of muQZ p attached to g : Gv p. -/
noncomputable def S2442MuQZEnd (g : Gv p) : muQZ p →+ muQZ p :=
  muQZ_lift p (muQZ p) (S2442MuQZEndFamily p g) (S2442MuQZEndFamily_compat p g)

/-- Computation rule for the endomorphism. -/
theorem S2442MuQZEnd_muQZof (g : Gv p) (H : Index p) (v : Stage p H) :
    S2442MuQZEnd p g (muQZof p H v) =
      muQZof p (S2169ConjIndex p g H) (S2179StageConj p g H v) :=
  muQZ_lift_of p (muQZ p) (S2442MuQZEndFamily p g)
    (S2442MuQZEndFamily_compat p g) H v

/-! ## 3. Functoriality of the torsion and abelianization coefficients -/

/-- The abelianization equivalence of a composite is the composite of the
abelianization equivalences. -/
theorem S2442_abelianizationCongr_trans {G H I : Type u} [Group G] [Group H] [Group I]
    (e₁ : G ≃* H) (e₂ : H ≃* I) :
    abelianizationCongr (e₁.trans e₂) =
      (abelianizationCongr e₁).trans (abelianizationCongr e₂) := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply]
  rfl

/-- Torsion congruence is functorial on elements. -/
theorem S2442_torsionCongr_trans {G H I : Type u} [CommGroup G] [CommGroup H] [CommGroup I]
    (e₁ : G ≃* H) (e₂ : H ≃* I) (w : CommGroup.torsion G) :
    torsionCongr e₂ (torsionCongr e₁ w) = torsionCongr (e₁.trans e₂) w := by
  apply Subtype.ext
  simp only [S2430_torsionCongr_coe, MulEquiv.trans_apply]

/-- The abelianization of the identity equivalence is the identity. -/
theorem S2442_abelianizationCongr_refl {G : Type u} [Group G] :
    abelianizationCongr (MulEquiv.refl G) = MulEquiv.refl (Abelianization G) := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext x
  rfl

/-- The torsion of the identity equivalence is the identity. -/
theorem S2442_torsionCongr_refl {G : Type u} [CommGroup G] :
    torsionCongr (MulEquiv.refl G) = MulEquiv.refl (CommGroup.torsion G) := by
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  rw [S2430_torsionCongr_coe]
  rfl

/-- Additive-stage version of the composition of two torsion coefficients. -/
theorem S2442_stageCongr_trans_apply {G : Type u} [Group G]
    {A B C : Subgroup G} (e₁ : ↥A ≃* ↥B) (e₂ : ↥B ≃* ↥C)
    (w : CommGroup.torsion (Abelianization ↥A)) :
    torsionCongr (abelianizationCongr e₂)
        (torsionCongr (abelianizationCongr e₁) w) =
      torsionCongr (abelianizationCongr (e₁.trans e₂)) w := by
  rw [S2442_torsionCongr_trans, ← S2442_abelianizationCongr_trans]

/-- Casting a torsion-congruence value along an equality of open subgroups,
controlled by the underlying element maps of the subgroup coefficients. -/
theorem S2442_stageCongr_index_cast_apply {H A B : Index p}
    (e : A = B) (eA : ↥H ≃* ↥A) (eB : ↥H ≃* ↥B)
    (h : ∀ x : ↥H, ((eA x : ↥A) : Gv p) = ((eB x : ↥B) : Gv p))
    (w : CommGroup.torsion (Abelianization ↥H)) :
    e ▸ (Additive.ofMul (torsionCongr (abelianizationCongr eA) w)) =
      Additive.ofMul (torsionCongr (abelianizationCongr eB) w) := by
  cases e
  have he : eA = eB := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact h x
  rw [he]

/-! ## 4. Composition of the actual stage conjugations -/

/-- Composition of the actual stage conjugations, with the open-subgroup
equality made explicit. -/
theorem S2442_stageConj_comp (g h : Gv p) (H : Index p) (v : Stage p H) :
    (S2442ConjIndex_comp p g h H) ▸
        (S2179StageConj p g (S2169ConjIndex p h H)
          (S2179StageConj p h H v)) =
      S2179StageConj p (h * g) H v := by
  let w : CommGroup.torsion (Abelianization ↥H) := Additive.toMul v
  have hv : v = Additive.ofMul w := rfl
  rw [hv]
  rw [S2430_stageConj_apply]
  rw [S2430_stageConj_apply]
  rw [S2430_stageConj_apply]
  rw [S2442_stageCongr_trans_apply]
  exact S2442_stageCongr_index_cast_apply (p := p) (H := H)
    (A := S2169ConjIndex p g (S2169ConjIndex p h H))
    (B := S2169ConjIndex p (h * g) H)
    (S2442ConjIndex_comp p g h H)
    ((S2200ConjEquiv p h H).trans (S2200ConjEquiv p g (S2169ConjIndex p h H)))
    (S2200ConjEquiv p (h * g) H)
    (by
      intro x
      rw [MulEquiv.trans_apply, S2317ConjEquiv_apply, S2317ConjEquiv_apply,
        S2317ConjEquiv_apply]
      group)
    w

/-- The stage conjugation by 1 is the identity, after the subgroup equality. -/
theorem S2442_stageConj_one_apply (H : Index p)
    (w : CommGroup.torsion (Abelianization ↥H)) :
    (S2442ConjIndex_one p H) ▸ (S2179StageConj p 1 H (Additive.ofMul w)) =
      Additive.ofMul w := by
  rw [S2430_stageConj_apply]
  have heq : (S2200ConjEquiv p 1 H) = MulEquiv.refl ↥H := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [S2317ConjEquiv_apply]
    rfl
  exact (S2442_stageCongr_index_cast_apply (p := p) (H := H)
      (A := S2169ConjIndex p 1 H) (B := H)
      (S2442ConjIndex_one p H) (S2200ConjEquiv p 1 H) (MulEquiv.refl ↥H)
      (by intro x; rw [S2317ConjEquiv_apply]; rfl) w).trans
    (by rw [S2442_abelianizationCongr_refl, S2442_torsionCongr_refl]; rfl)

/-! ## 5. The anti-composition law and the inverse -/

/-- Anti-composition law: A_g o A_h = A_(h*g). -/
theorem S2442MuQZEnd_comp (g h : Gv p) :
    (S2442MuQZEnd p g).comp (S2442MuQZEnd p h) = S2442MuQZEnd p (h * g) := by
  exact muQZ_lift_unique p (muQZ p) (S2442MuQZEndFamily p (h * g))
    (S2442MuQZEndFamily_compat p (h * g))
    ((S2442MuQZEnd p g).comp (S2442MuQZEnd p h))
    (by
      intro H v
      rw [AddMonoidHom.comp_apply, S2442MuQZEnd_muQZof, S2442MuQZEnd_muQZof]
      change muQZof p (S2169ConjIndex p g (S2169ConjIndex p h H))
          (S2179StageConj p g (S2169ConjIndex p h H)
            (S2179StageConj p h H v)) =
        muQZof p (S2169ConjIndex p (h * g) H) (S2179StageConj p (h * g) H v)
      exact (S2442_muQZof_cast (e := S2442ConjIndex_comp p g h H)
        (v := S2179StageConj p g (S2169ConjIndex p h H)
          (S2179StageConj p h H v))).trans
        (congrArg (muQZof p (S2169ConjIndex p (h * g) H))
          (S2442_stageConj_comp p g h H v)))

/-- The endomorphism attached to 1 is the identity. -/
theorem S2442MuQZEnd_one : S2442MuQZEnd p 1 = AddMonoidHom.id (muQZ p) := by
  have hcomp : ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      (fun H : Index p => muQZof p H) H (toStage p h v) =
        (fun H : Index p => muQZof p H) K v :=
    fun {H K} h v => muQZof_transfer p h v
  have h1 := muQZ_lift_unique p (muQZ p) (fun H : Index p => muQZof p H) hcomp
    (S2442MuQZEnd p 1) (by
      intro H v
      rw [S2442MuQZEnd_muQZof]
      have hv : v = Additive.ofMul (Additive.toMul v) := rfl
      rw [hv]
      exact (S2442_muQZof_cast (e := S2442ConjIndex_one p H)
        (v := S2179StageConj p 1 H (Additive.ofMul (Additive.toMul v)))).trans
        (congrArg (muQZof p H)
          (S2442_stageConj_one_apply p H (Additive.toMul v))))
  have h2 := muQZ_lift_unique p (muQZ p) (fun H : Index p => muQZof p H) hcomp
    (AddMonoidHom.id (muQZ p)) (fun H v => rfl)
  exact h1.trans h2.symm

/-- Inverse law, one order. -/
theorem S2442MuQZEnd_comp_inv (g : Gv p) :
    (S2442MuQZEnd p g).comp (S2442MuQZEnd p g⁻¹) =
      AddMonoidHom.id (muQZ p) := by
  rw [S2442MuQZEnd_comp, inv_mul_cancel, S2442MuQZEnd_one]

/-- Inverse law, the other order. -/
theorem S2442MuQZEnd_inv_comp (g : Gv p) :
    (S2442MuQZEnd p g⁻¹).comp (S2442MuQZEnd p g) =
      AddMonoidHom.id (muQZ p) := by
  rw [S2442MuQZEnd_comp, mul_inv_cancel, S2442MuQZEnd_one]

/-! ## 6. The honest MulAut action -/

/-- The additive equivalence underlying the action of g: A_(g^-1), with
inverse A_g. -/
noncomputable def S2442MuQZEndEquiv (g : Gv p) : muQZ p ≃+ muQZ p where
  toFun := S2442MuQZEnd p g⁻¹
  invFun := S2442MuQZEnd p g
  left_inv x := by
    have h := DFunLike.congr_fun (S2442MuQZEnd_comp_inv p g) x
    simpa [AddMonoidHom.comp_apply] using h
  right_inv x := by
    have h := DFunLike.congr_fun (S2442MuQZEnd_inv_comp p g) x
    simpa [AddMonoidHom.comp_apply] using h
  map_add' := map_add _

/-- The MulAut attached to g, acting by A_(g^-1). -/
noncomputable def S2442MulAutEnd (g : Gv p) :
    MulAut (Multiplicative (muQZ p)) :=
  (S2442MuQZEndEquiv p g).toMultiplicative

/-- Value formula for the action automorphism. -/
@[simp]
theorem S2442MulAutEnd_apply (g : Gv p) (x : Multiplicative (muQZ p)) :
    S2442MulAutEnd p g x =
      Multiplicative.ofAdd (S2442MuQZEnd p g⁻¹ (Multiplicative.toAdd x)) :=
  rfl

/-- The group law of the honest action: g |-> A_(g^-1) is multiplicative. -/
theorem S2442MulAutEnd_mul (g h : Gv p) :
    S2442MulAutEnd p (g * h) = S2442MulAutEnd p g * S2442MulAutEnd p h := by
  apply MulEquiv.ext
  intro x
  rw [MulAut.mul_apply]
  have hto : Multiplicative.toAdd (S2442MulAutEnd p (g * h) x) =
      Multiplicative.toAdd (S2442MulAutEnd p g (S2442MulAutEnd p h x)) := by
    rw [S2442MulAutEnd_apply, S2442MulAutEnd_apply, S2442MulAutEnd_apply,
      toAdd_ofAdd]
    rw [mul_inv_rev, ← S2442MuQZEnd_comp]
    rfl
  simpa using congrArg Multiplicative.ofAdd hto

/-- The honest monoid hom Gv p ->* MulAut (Multiplicative (muQZ p)). -/
noncomputable def S2442MuQZAction :
    Gv p →* MulAut (Multiplicative (muQZ p)) where
  toFun := S2442MulAutEnd p
  map_one' := by
    apply MulEquiv.ext
    intro x
    have h : Multiplicative.toAdd (S2442MulAutEnd p 1 x) =
        Multiplicative.toAdd ((1 : MulAut (Multiplicative (muQZ p))) x) := by
      rw [S2442MulAutEnd_apply, inv_one, S2442MuQZEnd_one]
      rfl
    simpa using congrArg Multiplicative.ofAdd h
  map_mul' := S2442MulAutEnd_mul p

/-- The honest compatibility: the action by g is the stage conjugation with
g^-1. -/
theorem S2442MuQZAction_compat (g : Gv p) (H : Index p) (v : Stage p H) :
    Multiplicative.toAdd (S2442MuQZAction p g
        (Multiplicative.ofAdd (muQZof p H v))) =
      muQZof p (S2169ConjIndex p g⁻¹ H) (S2179StageConj p g⁻¹ H v) := by
  show Multiplicative.toAdd (S2442MulAutEnd p g
      (Multiplicative.ofAdd (muQZof p H v))) = _
  rw [S2442MulAutEnd_apply, toAdd_ofAdd]
  exact S2442MuQZEnd_muQZof p g⁻¹ H v

/-! ## 7. Inner conjugation is trivial on the abelianization -/

/-- Conjugation in a group becomes the identity in the abelianization. -/
theorem S2442_abelianization_of_conj {G : Type u} [Group G] (a x : G) :
    Abelianization.of (a * x * a⁻¹) = Abelianization.of x := by
  rw [map_mul, map_mul, map_inv]
  rw [mul_comm (Abelianization.of a) (Abelianization.of x), mul_assoc,
    mul_inv_cancel, mul_one]

/-- The automorphism of H given by conjugation by an element g in H. -/
noncomputable def S2442InnerConj (g : Gv p) (H : Index p) (hg : g ∈ H) :
    ↥H ≃* ↥H where
  toFun x :=
    ⟨MulAut.conj g.symm (x : Gv p), by
      have hx : (x : Gv p) ∈ H := x.2
      have hg' : g.symm ∈ H := H.inv_mem hg
      have h : g.symm * (x : Gv p) * (g.symm)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem hg' hx) hg
      simpa [MulAut.conj_apply] using h⟩
  invFun x :=
    ⟨MulAut.conj g (x : Gv p), by
      have hx : (x : Gv p) ∈ H := x.2
      have h : g * (x : Gv p) * g⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
      simpa [MulAut.conj_apply] using h⟩
  left_inv x := by
    apply Subtype.ext
    change g * (g⁻¹ * (x : Gv p) * (g⁻¹)⁻¹) * g⁻¹ = (x : Gv p)
    group
  right_inv x := by
    apply Subtype.ext
    change g⁻¹ * (g * (x : Gv p) * g⁻¹) * (g⁻¹)⁻¹ = (x : Gv p)
    group
  map_mul' x y := by
    apply Subtype.ext
    simp [map_mul]

/-- Coercion formula for the inner conjugation equivalence. -/
@[simp]
theorem S2442InnerConj_apply_coe (g : Gv p) (H : Index p) (hg : g ∈ H)
    (x : ↥H) :
    ((S2442InnerConj p g H hg x : ↥H) : Gv p) =
      MulAut.conj g.symm (x : Gv p) :=
  rfl

/-- Coercion formula for S2200ConjEquiv on the ambient group. -/
theorem S2442ConjEquiv_coe (g : Gv p) (H : Index p) (x : ↥H) :
    ((S2200ConjEquiv p g H x : ↥(S2169ConjIndex p g H)) : Gv p) =
      MulAut.conj g.symm (x : Gv p) := by
  unfold S2200ConjEquiv S2173ConjSubgroupEquiv
  dsimp only
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply]

/-- The abelianization of the inner conjugation equivalence is the identity. -/
theorem S2442_abelianizationCongr_inner (g : Gv p) (H : Index p) (hg : g ∈ H) :
    abelianizationCongr (S2442InnerConj p g H hg) =
      MulEquiv.refl (Abelianization ↥H) := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext x
  change Abelianization.of (S2442InnerConj p g H hg x) = Abelianization.of x
  have hx : S2442InnerConj p g H hg x =
      (⟨g.symm, H.inv_mem hg⟩ : ↥H) * x * (⟨g.symm, H.inv_mem hg⟩ : ↥H)⁻¹ := by
    apply Subtype.ext
    rfl
  rw [hx]
  exact S2442_abelianization_of_conj (⟨g.symm, H.inv_mem hg⟩ : ↥H) x

/-- The stage conjugation by an element of H is the identity on the stage
of H, after transporting along the subgroup equality. -/
theorem S2442_stageConj_self_apply (g : Gv p) (H : Index p) (hg : g ∈ H)
    (v : Stage p H) :
    (S2442ConjIndex_self p g H hg) ▸ S2179StageConj p g H v = v := by
  let w : CommGroup.torsion (Abelianization ↥H) := Additive.toMul v
  have hv : v = Additive.ofMul w := rfl
  rw [hv]
  rw [S2430_stageConj_apply]
  rw [S2442_stageCongr_index_cast_apply (p := p) (H := H)
    (A := S2169ConjIndex p g H) (B := H)
    (e := S2442ConjIndex_self p g H hg)
    (eA := S2200ConjEquiv p g H)
    (eB := S2442InnerConj p g H hg)
    (h := by
      intro x
      rw [S2442ConjEquiv_coe, S2442InnerConj_apply_coe])
    w]
  rw [S2442_abelianizationCongr_inner, S2442_torsionCongr_refl]
  rfl

/-- An element of an open subgroup fixes every generator of its own stage. -/
theorem S2442_action_fixed (h : Gv p) (H : Index p) (hh : h ∈ H) (v : Stage p H) :
    S2442MuQZAction p h (Multiplicative.ofAdd (muQZof p H v)) =
      Multiplicative.ofAdd (muQZof p H v) := by
  apply Multiplicative.toAdd.injective
  rw [S2442MuQZAction_compat, Multiplicative.toAdd_ofAdd]
  have hmem : h⁻¹ ∈ H := H.inv_mem hh
  have e : S2169ConjIndex p h⁻¹ H = H := S2442ConjIndex_self p h⁻¹ H hmem
  rw [S2442_muQZof_cast (e := e)]
  congr 1
  exact S2442_stageConj_self_apply p h⁻¹ H hmem v

/-! ## 8. The available topology and joint continuity -/

/-- The discrete topology on muQZ p used by S2159 (up to the
Multiplicative type synonym). -/
abbrev S2442MuQZTopology : TopologicalSpace (muQZ p) := ⊥

/-- S2442's discrete topology agrees with S2159's declared topology. -/
theorem S2442MuQZTopology_eq : S2442MuQZTopology p = S2159MuQZTopology p :=
  rfl

/-- The source Gv p is discrete.  This proposition is not assumed and is
not used below; the topology instance in scope is the Krull topology. -/
def S2442SourceDiscrete : Prop := DiscreteTopology (Gv p)

/-- Joint continuity of the honest action for a topology T on muQZ p.
This is the precise exact first missing for the paper's non-discrete
(profinite) topology; it is assumed nowhere. -/
def S2442ActionJointContinuous (T : TopologicalSpace (muQZ p)) : Prop :=
  letI := T
  Continuous (fun q : Gv p × muQZ p =>
    Multiplicative.toAdd (S2442MuQZAction p q.1 (Multiplicative.ofAdd q.2)))

/-- The honest action is jointly continuous for the discrete topology of
S2159.  The source is not assumed discrete: for each point we use the open
subgroup H of a stage representative and the neighbourhood
g0 • H x {x0}. -/
theorem S2442ActionJointContinuous_discrete :
    S2442ActionJointContinuous p (S2442MuQZTopology p) := by
  letI : TopologicalSpace (muQZ p) := S2442MuQZTopology p
  haveI : DiscreteTopology (muQZ p) := discreteTopology_bot _
  change Continuous (fun q : Gv p × muQZ p =>
    Multiplicative.toAdd (S2442MuQZAction p q.1 (Multiplicative.ofAdd q.2)))
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨g0, x0⟩
  obtain ⟨H, v, rfl⟩ := muQZ_exists_stage p x0
  refine ⟨(g0 • (H : Set (Gv p))) ×ˢ ({muQZof p H v} : Set (muQZ p)),
    (H.isOpen.leftCoset g0).prod (isOpen_discrete _), ?_, ?_⟩
  · exact ⟨Set.mem_leftCoset g0 (one_mem H), rfl⟩
  · rintro ⟨g, x⟩ ⟨hg, hx⟩
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    have hh : g0⁻¹ * g ∈ H := (Set.mem_leftCoset_iff g0).mp hg
    have hg_eq : g = g0 * (g0⁻¹ * g) := by group
    rw [hg_eq]
    change Multiplicative.toAdd (S2442MuQZAction p (g0 * (g0⁻¹ * g))
        (Multiplicative.ofAdd (muQZof p H v))) =
      Multiplicative.toAdd (S2442MuQZAction p g0
        (Multiplicative.ofAdd (muQZof p H v)))
    rw [map_mul, MulAut.mul_apply, S2442_action_fixed p (g0⁻¹ * g) H hh v]

/-- The same continuity, stated with the topology appearing in S2159. -/
theorem S2442ActionJointContinuous_s2159 :
    S2442ActionJointContinuous p (S2159MuQZTopology p) := by
  rw [← S2442MuQZTopology_eq p]
  exact S2442ActionJointContinuous_discrete p

/-- The full MulAut data with the proved continuity field.  This records
the actual deliverable of this file without any topology missing. -/
structure S2442MuQZMulAutData where
  transfer_compat : S2179TransferCompatible (p := p)
  action : Gv p →* MulAut (Multiplicative (muQZ p))
  action_compat :
    ∀ (g : Gv p) (H : Index p) (v : Stage p H),
      Multiplicative.toAdd (action g (Multiplicative.ofAdd (muQZof p H v))) =
        muQZof p (S2169ConjIndex p g⁻¹ H) (S2179StageConj p g⁻¹ H v)
  action_continuous_discrete :
    letI : TopologicalSpace (muQZ p) := S2442MuQZTopology p
    Continuous (fun q : Gv p × muQZ p =>
      Multiplicative.toAdd (action q.1 (Multiplicative.ofAdd q.2)))

/-- Unconditional corrected data with honest action and discrete continuity. -/
noncomputable def S2442MuQZMulAutData_actual : S2442MuQZMulAutData p where
  transfer_compat := S2442_transferCompatible p
  action := S2442MuQZAction p
  action_compat := S2442MuQZAction_compat p
  action_continuous_discrete := S2442ActionJointContinuous_discrete p

/-! ## 9. Axiom probes -/

#check S2442_transferCompatible
#check S2442ConjIndex_self
#check S2442MuQZEnd
#check S2442MuQZEnd_muQZof
#check S2442MuQZEnd_comp
#check S2442MuQZEnd_comp_inv
#check S2442MuQZEnd_inv_comp
#check S2442MuQZAction
#check S2442MuQZAction_compat
#check S2442_action_fixed
#check S2442ActionJointContinuous
#check S2442ActionJointContinuous_discrete
#check S2442ActionJointContinuous_s2159
#check S2442MuQZMulAutData_actual

#print axioms S2442_transferCompatible
#print axioms S2442MuQZEnd
#print axioms S2442MuQZEnd_muQZof
#print axioms S2442MuQZEnd_comp
#print axioms S2442MuQZEnd_comp_inv
#print axioms S2442MuQZEnd_inv_comp
#print axioms S2442MuQZAction
#print axioms S2442MuQZAction_compat
#print axioms S2442_action_fixed
#print axioms S2442ActionJointContinuous_discrete
#print axioms S2442ActionJointContinuous_s2159
#print axioms S2442MuQZMulAutData_actual

end LeanFormal.IUT.XiFPaper.S2442ContinuitySubagentActual

end
