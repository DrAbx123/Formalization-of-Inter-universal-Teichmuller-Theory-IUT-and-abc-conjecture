import tmp.sheaf.xif.paper.S2189TransferCompatActual
import tmp.sheaf.xif.paper.S2371HnatExplicitActual

/-!
# S2431: the additive action of Gv p on muQZ p and the MulAut data

Layer: O (Theta-link / q-pilot).  Consumers:
S2189TransferCompatActual.S2189MuQZMulAutData (Task B of the S2189 package),
S2159MuQZActionActual.S2159TopologicalModuleDataOf, and the S2159/S2131
topological-module chain.

## What is proved here (unconditional, no sorry, no axiom)

* S2431_transferCompatible: the S2179 transfer-compatibility statement.
  It is reduced to S2371_verlagerung_natural by identifying the underlying
  abelianization coefficient of S2179StageConj with S2200ConjEquiv
  (S2431_stageConj_eq) and restricting the naturality square to
  CommGroup.torsion.
* S2431MuQZEnd: the additive endomorphism of muQZ p attached to g : Gv p,
  obtained from muQZ_lift with the stage conjugation family.  Its computation
  rule is S2431MuQZEnd_muQZof.
* S2431ConjIndex_comp: conj_g (conj_h H) = conj_(h*g) H on open subgroups.
* S2431_stageCongr_trans_apply / S2431_stageCongr_index_cast_apply: the
  torsion-stage bookkeeping that makes the composition law statable;
  S2431_stageConj_comp is the resulting composition of the actual stage
  conjugation equivalences.
* S2431MuQZEnd_comp: the anti-composition law A_g o A_h = A_(h*g).
  Consequently A_g is an additive equivalence with inverse A_(g^-1)
  (S2431MuQZEnd_comp_inv, S2431MuQZEnd_inv_comp).
* S2431MuQZAction: the honest monoid hom
  Gv p ->* MulAut (Multiplicative (muQZ p)), g |-> A_(g^-1), with
  S2431MuQZAction_compat and joint continuity for the discrete topology
  (S2431MuQZAction_continuous).
* S2431MuQZMulAutData_actual: the corrected S2189-shaped data with the
  g^-1 indexing supplied by the honest action.
* S2431S2189MuQZMulAutDataOfComm: S2189MuQZMulAutData p from the
  commutativity hypothesis hcomm : A_(g*h) = A_(h*g).

## The exact first missing, separated by field

* (inverse)  done: S2431MuQZEnd_comp_inv, S2431MuQZEnd_inv_comp.
* (group law) done, with the inverse convention: S2431MuQZEnd_comp gives
  A_g o A_h = A_(h*g); the honest monoid-hom action is g |-> A_(g^-1)
  (S2431MuQZAction).  A monoid hom with action g = A_g is equivalent to
  S2431EndComm, i.e. A_(g*h) = A_(h*g) for all g h.
* (continuity) done for the topology used in the tree: the source S2159 puts
  the discrete topology on Multiplicative (muQZ p), and for a discrete target
  every function is continuous (S2431MuQZAction_continuous).  The nontrivial
  joint continuity (M5 of S2017) is not statable in the tree (no
  profinite/adelic topology on muQZ p is declared).
* (equivariance) the S2189 field action_compat is stated with the g-indexed
  stage S2179StageConj g H; the actual conjugation supplies the g^-1-indexed
  stage.  The literal field is therefore not the honest action.
  S2431MuQZMulAutData_actual records the honest action and
  S2431S2189MuQZMulAutDataOfComm produces the literal S2189 structure from
  S2431EndComm; conversely S2431EndComm_of_s2189 shows the literal structure
  forces that input.  For the S2159/S2131 equivariance the missing inputs are
  muHatComparison p and the comparison equation heq, exactly as in
  S2159TopologicalModuleDataOf.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2431MuQZMulAutSubagentActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2317SubgroupOfApplyActual
open LeanFormal.IUT.XiFPaper.S2338TransferCompatDoneActual
open LeanFormal.IUT.XiFPaper.S2371HnatExplicitActual
open LeanFormal.IUT.XiFPaper.S2189TransferCompatActual

universe u

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. Torsion bookkeeping for the stage conjugations -/

/-- Transporting a MulEquiv of subgroups along an equality of the target
subgroups agrees with composing with MulEquiv.subgroupCongr. -/
theorem S2431_cast_equiv_eq_trans {G : Type u} [Group G]
    {X A B : Subgroup G} (h : A = B) (e : ↥X ≃* ↥A) :
    (h ▸ e : ↥X ≃* ↥B) = e.trans (MulEquiv.subgroupCongr h) := by
  cases h
  ext x
  rfl

/-- Coercion formula for the torsion equivalence induced by a multiplicative
equivalence. -/
theorem S2431_torsionCongr_coe {A : Type u} {B : Type u} [CommGroup A] [CommGroup B]
    (e : A ≃* B) (w : CommGroup.torsion A) :
    ((torsionCongr e w : CommGroup.torsion B) : B) = e (w : A) :=
  rfl

/-- Coercion formula for the restriction of a homomorphism to torsion. -/
theorem S2431_torsionMap_coe {A : Type u} {B : Type u} [CommGroup A] [CommGroup B]
    (f : A →* B) (w : CommGroup.torsion A) :
    ((torsionMap f w : CommGroup.torsion B) : B) = f (w : A) :=
  rfl

/-- The additive transfer map toStage on a torsion element. -/
theorem S2431_toStage_apply {H K : Index p} (h : H ≤ K)
    (w : CommGroup.torsion (Abelianization ↥K)) :
    toStage p h (Additive.ofMul w) =
      Additive.ofMul (torsionMap (verlagerungOpen p h) w) :=
  rfl

/-- On generators, the abelianization equivalence induced by e is e. -/
theorem S2431_abelianizationCongr_of {G : Type u} {H : Type u} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    abelianizationCongr e (Abelianization.of x) = Abelianization.of (e x) :=
  rfl

/-- Equality of multiplicative equivalences from pointwise equality. -/
theorem S2431_torsionCongr_congr {A : Type u} {B : Type u} [CommGroup A] [CommGroup B]
    {e₁ e₂ : A ≃* B} (h : ∀ x, e₁ x = e₂ x) :
    torsionCongr e₁ = torsionCongr e₂ := by
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  rw [S2431_torsionCongr_coe, S2431_torsionCongr_coe]
  exact h (w : A)

/-- Equality of abelianization equivalences from pointwise equality. -/
theorem S2431_abelianizationCongr_congr {G : Type u} {H : Type u} [Group G] [Group H]
    {e₁ e₂ : G ≃* H} (h : ∀ x, e₁ x = e₂ x) :
    abelianizationCongr e₁ = abelianizationCongr e₂ := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    S2431_abelianizationCongr_of, h x]

/-- The abelianization equivalence of a composite is the composite of the
abelianization equivalences. -/
theorem S2431_abelianizationCongr_trans {G : Type u} {H : Type u} {I : Type u}
    [Group G] [Group H] [Group I]
    (e₁ : G ≃* H) (e₂ : H ≃* I) :
    abelianizationCongr (e₁.trans e₂) =
      (abelianizationCongr e₁).trans (abelianizationCongr e₂) := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    S2431_abelianizationCongr_of, MulEquiv.trans_apply]

/-- The torsion coefficient of S2179StageConj is the torsion coefficient of
S2200ConjEquiv. -/
theorem S2431_stageConj_eq (g : Gv p) (H : Index p) :
    S2179StageConj p g H =
      (torsionCongr (abelianizationCongr (S2200ConjEquiv p g H))).toAdditive := by
  unfold S2179StageConj
  dsimp only
  rw [S2431_cast_equiv_eq_trans]
  rfl

/-- Pointwise form of S2431_stageConj_eq on a torsion element. -/
theorem S2431_stageConj_apply (g : Gv p) (H : Index p)
    (w : CommGroup.torsion (Abelianization ↥H)) :
    S2179StageConj p g H (Additive.ofMul w) =
      Additive.ofMul (torsionCongr (abelianizationCongr (S2200ConjEquiv p g H)) w) := by
  rw [S2431_stageConj_eq]

/-- Additive-stage version of the composition of two torsion coefficients. -/
theorem S2431_stageCongr_trans_apply {G : Type u} [Group G]
    {A B C : Subgroup G} (e₁ : ↥A ≃* ↥B) (e₂ : ↥B ≃* ↥C)
    (w : CommGroup.torsion (Abelianization ↥A)) :
    torsionCongr (abelianizationCongr e₂)
        (torsionCongr (abelianizationCongr e₁) w) =
      torsionCongr (abelianizationCongr (e₁.trans e₂)) w := by
  apply Subtype.ext
  simp only [S2431_torsionCongr_coe]
  rw [S2431_abelianizationCongr_trans]
  rfl

/-- Casting a torsion stage along an equality of open subgroups, controlled by
the underlying element maps of the subgroup coefficients. -/
theorem S2431_stageCongr_index_cast_apply {H A B : Index p}
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

/-! ## 2. Transfer compatibility (the S2179 target) -/

/-- Transfer compatibility: the stage conjugation is compatible with the
Verlagerung, i.e. S2179TransferCompatible holds. -/
theorem S2431_transferCompatible : S2179TransferCompatible (p := p) := by
  intro g H K h v
  obtain ⟨h', hnat⟩ := (S2371_verlagerung_natural (p := p)) g H K h
  refine ⟨h', ?_⟩
  let w : CommGroup.torsion (Abelianization ↥K) := Additive.toMul v
  have hv : v = Additive.ofMul w := rfl
  rw [hv, S2431_toStage_apply, S2431_stageConj_apply, S2431_stageConj_apply,
    S2431_toStage_apply]
  apply Additive.ext
  apply Subtype.ext
  simp only [S2431_torsionCongr_coe, S2431_torsionMap_coe]
  exact DFunLike.congr_fun hnat (w : Abelianization ↥K)

/-! ## 3. The additive endomorphism attached to g -/

/-- The levelwise family defining the endomorphism of muQZ p attached to
g : Gv p. -/
noncomputable def S2431MuQZEndFamily (g : Gv p) :
    ∀ H : Index p, Stage p H →+ muQZ p :=
  fun H =>
    (muQZof p (S2169ConjIndex p g H)).comp
      (S2179StageConj p g H).toAddMonoidHom

/-- The compatibility needed for muQZ_lift, from transfer compatibility. -/
theorem S2431MuQZEndFamily_compat (g : Gv p) :
    ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      S2431MuQZEndFamily p g H (toStage p h v) =
        S2431MuQZEndFamily p g K v := by
  intro H K h v
  obtain ⟨h', hEq⟩ := S2431_transferCompatible (p := p) g H K h v
  change muQZof p (S2169ConjIndex p g H)
      (S2179StageConj p g H (toStage p h v)) =
    muQZof p (S2169ConjIndex p g K) (S2179StageConj p g K v)
  rw [hEq, muQZof_transfer (p := p) (H := S2169ConjIndex p g H)
    (K := S2169ConjIndex p g K) h']

/-- The additive endomorphism of muQZ p attached to g : Gv p. -/
noncomputable def S2431MuQZEnd (g : Gv p) : muQZ p →+ muQZ p :=
  muQZ_lift p (muQZ p) (S2431MuQZEndFamily p g) (S2431MuQZEndFamily_compat p g)

/-- Computation rule for the endomorphism. -/
theorem S2431MuQZEnd_muQZof (g : Gv p) (H : Index p) (v : Stage p H) :
    S2431MuQZEnd p g (muQZof p H v) =
      muQZof p (S2169ConjIndex p g H) (S2179StageConj p g H v) :=
  muQZ_lift_of p (muQZ p) (S2431MuQZEndFamily p g)
    (S2431MuQZEndFamily_compat p g) H v

/-! ## 4. Composition of the open-subgroup conjugation and of the stages -/

/-- Conjugating twice composes the open subgroups: conj_g (conj_h H) is
conj_(h*g) H. -/
theorem S2431ConjIndex_comp (g h : Gv p) (H : Index p) :
    S2169ConjIndex p g (S2169ConjIndex p h H) = S2169ConjIndex p (h * g) H := by
  apply OpenSubgroup.ext
  intro x
  simp only [S2169ConjIndex, OpenSubgroup.mem_comap, MulAut.conj_apply]
  have hkey : h * (g * x * g⁻¹) * h⁻¹ = h * g * x * (h * g)⁻¹ := by group
  rw [hkey]

/-- muQZof is invariant under an equality of open subgroups. -/
theorem S2431_muQZof_cast {H H' : Index p} (e : H = H') (v : Stage p H) :
    muQZof p H v = muQZof p H' (e ▸ v) := by
  cases e
  rfl

/-- Composition of the actual stage conjugations, with the open-subgroup
equality made explicit. -/
theorem S2431_stageConj_comp (g h : Gv p) (H : Index p) (v : Stage p H) :
    (S2431ConjIndex_comp p g h H) ▸
        (S2179StageConj p g (S2169ConjIndex p h H)
          (S2179StageConj p h H v)) =
      S2179StageConj p (h * g) H v := by
  let w : CommGroup.torsion (Abelianization ↥H) := Additive.toMul v
  have hv : v = Additive.ofMul w := rfl
  rw [hv]
  rw [S2431_stageConj_apply]
  rw [S2431_stageConj_apply]
  rw [S2431_stageCongr_trans_apply]
  exact S2431_stageCongr_index_cast_apply (p := p) (H := H)
    (A := S2169ConjIndex p g (S2169ConjIndex p h H))
    (B := S2169ConjIndex p (h * g) H)
    (S2431ConjIndex_comp p g h H)
    ((S2200ConjEquiv p h H).trans (S2200ConjEquiv p g (S2169ConjIndex p h H)))
    (S2200ConjEquiv p (h * g) H)
    (by
      intro x
      rw [MulEquiv.trans_apply, S2317ConjEquiv_apply, S2317ConjEquiv_apply,
        S2317ConjEquiv_apply]
      group)
    w

/-! ## 5. The anti-composition law and the inverse -/

/-- Anti-composition law: A_g o A_h = A_(h*g). -/
theorem S2431MuQZEnd_comp (g h : Gv p) :
    (S2431MuQZEnd p g).comp (S2431MuQZEnd p h) = S2431MuQZEnd p (h * g) := by
  exact muQZ_lift_unique p (muQZ p) (S2431MuQZEndFamily p (h * g))
    (S2431MuQZEndFamily_compat p (h * g))
    ((S2431MuQZEnd p g).comp (S2431MuQZEnd p h))
    (by
      intro H v
      rw [AddMonoidHom.comp_apply, S2431MuQZEnd_muQZof, S2431MuQZEnd_muQZof,
        S2431MuQZEnd_muQZof]
      rw [S2431_muQZof_cast (e := S2431ConjIndex_comp p g h H)]
      rw [S2431_stageConj_comp])

/-- The open-subgroup conjugation by 1 is the identity. -/
theorem S2431ConjIndex_one (H : Index p) :
    S2169ConjIndex p 1 H = H := by
  apply OpenSubgroup.ext
  intro x
  simp [S2169ConjIndex, MulAut.conj_apply]

/-- The stage conjugation by 1 is the identity, after the subgroup equality. -/
theorem S2431_stageConj_one_apply (H : Index p)
    (w : CommGroup.torsion (Abelianization ↥H)) :
    (S2431ConjIndex_one p H) ▸ (S2179StageConj p 1 H (Additive.ofMul w)) =
      Additive.ofMul w := by
  rw [S2431_stageConj_apply]
  have hrefl : torsionCongr (abelianizationCongr (MulEquiv.refl ↥H)) w = w := by
    apply Subtype.ext
    simp only [S2431_torsionCongr_coe]
    rfl
  rw [S2431_stageCongr_index_cast_apply (p := p) (H := H)
    (A := S2169ConjIndex p 1 H) (B := H)
    (S2431ConjIndex_one p H)
    (S2200ConjEquiv p 1 H) (MulEquiv.refl ↥H)
    (by
      intro x
      rw [S2317ConjEquiv_apply]
      simp)
    w]
  rw [hrefl]

/-- The endomorphism attached to 1 is the identity. -/
theorem S2431MuQZEnd_one : S2431MuQZEnd p 1 = AddMonoidHom.id (muQZ p) := by
  have hcomp : ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      (fun H : Index p => muQZof p H) H (toStage p h v) =
        (fun H : Index p => muQZof p H) K v :=
    fun {H K} h v => muQZof_transfer p h v
  have h1 := muQZ_lift_unique p (muQZ p) (fun H : Index p => muQZof p H) hcomp
    (S2431MuQZEnd p 1) (by
      intro H v
      rw [S2431MuQZEnd_muQZof]
      let w : CommGroup.torsion (Abelianization ↥H) := Additive.toMul v
      have hv : v = Additive.ofMul w := rfl
      rw [hv]
      rw [S2431_muQZof_cast (e := S2431ConjIndex_one p H)]
      rw [S2431_stageConj_one_apply]
      rw [hv])
  have h2 := muQZ_lift_unique p (muQZ p) (fun H : Index p => muQZof p H) hcomp
    (AddMonoidHom.id (muQZ p)) (fun H v => rfl)
  exact h1.trans h2.symm

/-- Inverse law, one order. -/
theorem S2431MuQZEnd_comp_inv (g : Gv p) :
    (S2431MuQZEnd p g).comp (S2431MuQZEnd p g⁻¹) =
      AddMonoidHom.id (muQZ p) := by
  rw [S2431MuQZEnd_comp]
  rw [inv_mul_cancel g]
  exact S2431MuQZEnd_one p

/-- Inverse law, the other order. -/
theorem S2431MuQZEnd_inv_comp (g : Gv p) :
    (S2431MuQZEnd p g⁻¹).comp (S2431MuQZEnd p g) =
      AddMonoidHom.id (muQZ p) := by
  rw [S2431MuQZEnd_comp]
  rw [mul_inv_cancel g]
  exact S2431MuQZEnd_one p

/-! ## 6. The MulAut action -/

/-- The additive equivalence underlying the action of g: A_(g^-1), with
inverse A_g. -/
noncomputable def S2431MuQZEndEquiv (g : Gv p) : muQZ p ≃+ muQZ p where
  toFun := S2431MuQZEnd p g⁻¹
  invFun := S2431MuQZEnd p g
  left_inv x := by
    have h := DFunLike.congr_fun (S2431MuQZEnd_comp_inv p g) x
    simpa [AddMonoidHom.comp_apply] using h
  right_inv x := by
    have h := DFunLike.congr_fun (S2431MuQZEnd_inv_comp p g) x
    simpa [AddMonoidHom.comp_apply] using h
  map_add' := map_add _

/-- The value formula for the action automorphism. -/
theorem S2431MuQZEndEquiv_toMultiplicative_apply (g : Gv p)
    (x : Multiplicative (muQZ p)) :
    (S2431MuQZEndEquiv p g).toMultiplicative x =
      Multiplicative.ofAdd (S2431MuQZEnd p g⁻¹ (Multiplicative.toAdd x)) :=
  rfl

/-- The MulAut attached to g, acting by A_(g^-1). -/
noncomputable def S2431MulAutEnd (g : Gv p) :
    MulAut (Multiplicative (muQZ p)) :=
  (S2431MuQZEndEquiv p g).toMultiplicative

/-- Value formula for the action automorphism. -/
@[simp]
theorem S2431MulAutEnd_apply (g : Gv p) (x : Multiplicative (muQZ p)) :
    S2431MulAutEnd p g x =
      Multiplicative.ofAdd (S2431MuQZEnd p g⁻¹ (Multiplicative.toAdd x)) :=
  rfl

/-- The group law of the honest action: g |-> A_(g^-1) is multiplicative. -/
theorem S2431MulAutEnd_mul (g h : Gv p) :
    S2431MulAutEnd p (g * h) = S2431MulAutEnd p g * S2431MulAutEnd p h := by
  apply MulEquiv.ext
  intro x
  apply Multiplicative.ofAdd.injective
  rw [S2431MulAutEnd_apply, MulAut.mul_apply, S2431MulAutEnd_apply,
    S2431MulAutEnd_apply]
  simp only [Multiplicative.toAdd_ofAdd]
  rw [mul_inv_rev]
  rw [← S2431MuQZEnd_comp]

/-- The honest monoid hom Gv p ->* MulAut (Multiplicative (muQZ p)). -/
noncomputable def S2431MuQZAction :
    Gv p →* MulAut (Multiplicative (muQZ p)) where
  toFun := S2431MulAutEnd p
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Multiplicative.ofAdd.injective
    rw [S2431MulAutEnd_apply]
    simp only [Multiplicative.toAdd_ofAdd, inv_one, S2431MuQZEnd_one,
      AddMonoidHom.id_apply]
  map_mul' := S2431MulAutEnd_mul p

/-- The honest compatibility: the action by g is the stage conjugation with
g^-1. -/
theorem S2431MuQZAction_compat (g : Gv p) (H : Index p) (v : Stage p H) :
    Multiplicative.toAdd (S2431MuQZAction p g
        (Multiplicative.ofAdd (muQZof p H v))) =
      muQZof p (S2169ConjIndex p g⁻¹ H) (S2179StageConj p g⁻¹ H v) := by
  rw [show S2431MuQZAction p g = S2431MulAutEnd p g from rfl]
  rw [S2431MulAutEnd_apply]
  simp only [Multiplicative.toAdd_ofAdd]
  exact S2431MuQZEnd_muQZof p g⁻¹ H v

/-- Continuity for the topology used in the tree: S2159 puts the discrete
topology on Multiplicative (muQZ p), and any map into a discrete space is
continuous. -/
theorem S2431MuQZAction_continuous :
    letI : TopologicalSpace (muQZ p) := ⊥
    Continuous (fun q : Gv p × muQZ p =>
      Multiplicative.toAdd (S2431MuQZAction p q.1
        (Multiplicative.ofAdd q.2))) := by
  letI : TopologicalSpace (muQZ p) := ⊥
  haveI : DiscreteTopology (muQZ p) := discreteTopology_bot _
  exact continuous_of_discreteTopology

/-! ## 7. The corrected S2189-shaped data and the literal S2189 structure -/

/-- The exact commutativity input which turns the anti-action into a genuine
g-indexed monoid hom. -/
def S2431EndComm : Prop :=
  ∀ g h : Gv p, S2431MuQZEnd p (g * h) = S2431MuQZEnd p (h * g)

/-- The corrected S2189-shaped data: the honest action and its g^-1
compatibility. -/
structure S2431MuQZMulAutData where
  transfer_compat : S2179TransferCompatible (p := p)
  action : Gv p →* MulAut (Multiplicative (muQZ p))
  action_compat :
    ∀ (g : Gv p) (H : Index p) (v : Stage p H),
      Multiplicative.toAdd (action g (Multiplicative.ofAdd (muQZof p H v))) =
        muQZof p (S2169ConjIndex p g⁻¹ H) (S2179StageConj p g⁻¹ H v)

/-- Unconditional corrected data. -/
noncomputable def S2431MuQZMulAutData_actual : S2431MuQZMulAutData p where
  transfer_compat := S2431_transferCompatible p
  action := S2431MuQZAction p
  action_compat := S2431MuQZAction_compat p

/-- The direct g-indexed action automorphism, acting by A_g. -/
noncomputable def S2431MulAutEndDirect (g : Gv p) :
    MulAut (Multiplicative (muQZ p)) where
  toFun x := Multiplicative.ofAdd (S2431MuQZEnd p g (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (S2431MuQZEnd p g⁻¹ (Multiplicative.toAdd x))
  left_inv x := by
    have h := DFunLike.congr_fun (S2431MuQZEnd_comp_inv p g) (Multiplicative.toAdd x)
    simpa using congrArg Multiplicative.ofAdd h
  right_inv x := by
    have h := DFunLike.congr_fun (S2431MuQZEnd_inv_comp p g) (Multiplicative.toAdd x)
    simpa using congrArg Multiplicative.ofAdd h
  map_mul' x y := by
    apply Multiplicative.ofAdd.injective
    simp only [Multiplicative.toAdd_ofAdd, Multiplicative.toAdd_mul, map_add]

/-- Value formula for the direct action automorphism. -/
@[simp]
theorem S2431MulAutEndDirect_apply (g : Gv p) (x : Multiplicative (muQZ p)) :
    S2431MulAutEndDirect p g x =
      Multiplicative.ofAdd (S2431MuQZEnd p g (Multiplicative.toAdd x)) :=
  rfl

/-- Under S2431EndComm the direct action is a monoid hom. -/
noncomputable def S2431MuQZActionDirect (hcomm : S2431EndComm p) :
    Gv p →* MulAut (Multiplicative (muQZ p)) where
  toFun := S2431MulAutEndDirect p
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Multiplicative.ofAdd.injective
    rw [S2431MulAutEndDirect_apply]
    simp only [Multiplicative.toAdd_ofAdd, one_inv, S2431MuQZEnd_one,
      AddMonoidHom.id_apply]
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    apply Multiplicative.ofAdd.injective
    rw [S2431MulAutEndDirect_apply, MulAut.mul_apply, S2431MulAutEndDirect_apply,
      S2431MulAutEndDirect_apply]
    simp only [Multiplicative.toAdd_ofAdd]
    rw [hcomm g h, ← S2431MuQZEnd_comp g h]
    rfl

/-- The direct action satisfies the literal S2189 compatibility. -/
theorem S2431MuQZActionDirect_compat (hcomm : S2431EndComm p)
    (g : Gv p) (H : Index p) (v : Stage p H) :
    Multiplicative.toAdd (S2431MuQZActionDirect p hcomm g
        (Multiplicative.ofAdd (muQZof p H v))) =
      muQZof p (S2169ConjIndex p g H) (S2179StageConj p g H v) := by
  rw [show S2431MuQZActionDirect p hcomm g = S2431MulAutEndDirect p g from rfl]
  rw [S2431MulAutEndDirect_apply]
  simp only [Multiplicative.toAdd_ofAdd]
  exact S2431MuQZEnd_muQZof p g H v

/-- Conditional construction of the literal S2189MuQZMulAutData: the only
extra input beyond transfer compatibility is S2431EndComm. -/
noncomputable def S2431S2189MuQZMulAutDataOfComm (hcomm : S2431EndComm p) :
    S2189MuQZMulAutData p where
  transfer_compat := S2431_transferCompatible p
  action := S2431MuQZActionDirect p hcomm
  action_compat := S2431MuQZActionDirect_compat p hcomm

/-- The additive map underlying a MulAut of a Multiplicative type. -/
noncomputable def S2431AddOfMulAut (f : MulAut (Multiplicative (muQZ p))) :
    muQZ p →+ muQZ p where
  toFun x := Multiplicative.toAdd (f (Multiplicative.ofAdd x))
  map_zero' := by
    rw [← Multiplicative.ofAdd.injective.eq_iff]
    simp
  map_add' x y := by
    rw [← Multiplicative.ofAdd.injective.eq_iff]
    simp [map_mul, ofAdd_add]

/-- Value formula for S2431AddOfMulAut. -/
@[simp]
theorem S2431AddOfMulAut_apply (f : MulAut (Multiplicative (muQZ p))) (x : muQZ p) :
    S2431AddOfMulAut p f x = Multiplicative.toAdd (f (Multiplicative.ofAdd x)) :=
  rfl

/-- Its values on generators are exactly the stage conjugation, hence it is A_g
by uniqueness of the colimit map. -/
theorem S2431AddOfMulAut_eq (D : S2189MuQZMulAutData p) (g : Gv p) :
    S2431AddOfMulAut p (S2189MuQZMulAutData.action D g) = S2431MuQZEnd p g := by
  apply muQZ_lift_unique p (muQZ p) (S2431MuQZEndFamily p g)
    (S2431MuQZEndFamily_compat p g)
  intro H v
  rw [S2431AddOfMulAut_apply]
  change Multiplicative.toAdd
      (S2189MuQZMulAutData.action D g (Multiplicative.ofAdd (muQZof p H v))) =
    S2431MuQZEndFamily p g H v
  rw [S2189MuQZMulAutData.action_compat D g H v]
  rfl

/-- The literal S2189 data forces the commutativity input: any
S2189MuQZMulAutData yields S2431EndComm. -/
theorem S2431EndComm_of_s2189 (D : S2189MuQZMulAutData p) : S2431EndComm p := by
  intro g h
  have hlaw := map_mul (S2189MuQZMulAutData.action D) g h
  have h1 : S2431AddOfMulAut p (S2189MuQZMulAutData.action D (g * h)) =
      (S2431AddOfMulAut p (S2189MuQZMulAutData.action D g)).comp
        (S2431AddOfMulAut p (S2189MuQZMulAutData.action D h)) := by
    rw [← hlaw]
    rfl
  rw [S2431AddOfMulAut_eq p D (g * h), S2431AddOfMulAut_eq p D g,
    S2431AddOfMulAut_eq p D h] at h1
  rw [h1, S2431MuQZEnd_comp]

#check S2431_transferCompatible
#check S2431MuQZEnd
#check S2431MuQZEnd_muQZof
#check S2431ConjIndex_comp
#check S2431_stageConj_comp
#check S2431MuQZEnd_comp
#check S2431MuQZEnd_comp_inv
#check S2431MuQZEnd_inv_comp
#check S2431MuQZAction
#check S2431MuQZAction_compat
#check S2431MuQZAction_continuous
#check S2431MuQZMulAutData
#check S2431MuQZMulAutData_actual
#check S2431S2189MuQZMulAutDataOfComm
#check S2431EndComm_of_s2189

#print axioms S2431_transferCompatible
#print axioms S2431MuQZEnd
#print axioms S2431MuQZEnd_muQZof
#print axioms S2431ConjIndex_comp
#print axioms S2431_stageConj_comp
#print axioms S2431MuQZEnd_comp
#print axioms S2431MuQZEnd_one
#print axioms S2431MuQZEnd_comp_inv
#print axioms S2431MuQZEnd_inv_comp
#print axioms S2431MuQZAction
#print axioms S2431MuQZAction_compat
#print axioms S2431MuQZAction_continuous
#print axioms S2431MuQZMulAutData_actual
#print axioms S2431S2189MuQZMulAutDataOfComm
#print axioms S2431EndComm_of_s2189

end LeanFormal.IUT.XiFPaper.S2431MuQZMulAutSubagentActual

end
