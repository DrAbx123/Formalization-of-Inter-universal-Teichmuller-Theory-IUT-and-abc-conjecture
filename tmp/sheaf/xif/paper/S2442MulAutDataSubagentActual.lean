import tmp.sheaf.xif.paper.S2017VerlagerungActual
import tmp.sheaf.xif.paper.S2159MuQZActionActual
import tmp.sheaf.xif.paper.S2169MuQZConjugationActual
import tmp.sheaf.xif.paper.S2173StageConjugationActual
import tmp.sheaf.xif.paper.S2179StageConjEquivActual
import tmp.sheaf.xif.paper.S2189TransferCompatActual
import tmp.sheaf.xif.paper.S2200TransferNaturalityActual
import tmp.sheaf.xif.paper.S2317SubgroupOfApplyActual
import tmp.sheaf.xif.paper.S2430TorsionDescentSubagentActual

/-!
# S2442: honest g-inverse-indexed multiplicative data on muQZ p

Layer: O (Theta-link / q-pilot).  Consumer: the S2189 muQZ MulAut
surface consumed by the transfer/cyclotome chain.

Status of imports: this file is a fresh actual development.  It does not
import the unfinished S2431MuQZMulAutSubagentActual.lean and it does not
import S2432MuQZMulAutDoneActual.lean; every declaration below is proved
from the lower layers (S2017, S2159, S2169, S2173, S2179, S2200, S2317,
S2430).  In particular the unconditional transfer compatibility
S2179TransferCompatible is the already closed S2430_transferCompatible.

## What is constructed

* S2442ConjIndex_comp, S2442ConjIndex_one: the open-subgroup conjugation
  S2169ConjIndex is a right action up to the anti-composition law
  conj_g (conj_h H) = conj_(h*g) H.
* S2442MuQZEnd: for g : Gv p, the additive endomorphism
  A_g : muQZ p ->+ muQZ p obtained from muQZ_lift and the actual stage
  conjugation S2179StageConj, with computation rule
  S2442MuQZEnd_muQZof.
* S2442_stageConj_comp and S2442MuQZEnd_comp: the actual stage
  conjugations and the endomorphisms satisfy A_g o A_h = A_(h*g).
* S2442MuQZEnd_one, S2442MuQZEnd_comp_inv, S2442MuQZEnd_inv_comp:
  A_1 = id and the two inverse laws.  Hence
  S2442MuQZEndEquiv g : muQZ p =+ muQZ p with toFun = A_(g-inverse).
* S2442MuQZAction : Gv p ->* MulAut (Multiplicative (muQZ p)), the honest
  action g |-> A_(g-inverse), with the honest g-inverse-indexed
  compatibility S2442MuQZAction_compat.  It inhabits
  S2159MuQZActionRequired.
* S2442MuQZMulAutData: the honest data structure (transfer compatibility,
  action, g-inverse-indexed action_compat), inhabited unconditionally by
  S2442MuQZMulAutData_actual.

## The literal S2189 structure

The literal S2189MuQZMulAutData is stated with a g-indexed action_compat.
For the honest action this is available exactly under the commutativity
input

  S2442EndComm p : forall g h, A_(g*h) = A_(h*g),

see S2442MuQZActionDirect, S2442MuQZActionDirect_compat,
S2442S2189MuQZMulAutDataOfComm.  Conversely any literal
S2189MuQZMulAutData forces S2442EndComm p
(S2442EndComm_of_s2189).  Thus S2442EndComm is the exact first missing
for the literal g-indexed S2189 structure; it is assumed nowhere in this
file and the honest structure above is unconditional.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2442MulAutDataSubagentActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2159MuQZActionActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2189TransferCompatActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2317SubgroupOfApplyActual
open LeanFormal.IUT.XiFPaper.S2430TorsionDescentSubagentActual

universe u

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. Transfer compatibility and the open-subgroup conjugation -/

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

/-! ## 6. The honest MulAut action and its g-inverse-compatibility -/

/-- The additive equivalence underlying the action of g: A_(g-inverse), with
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

/-- The MulAut attached to g, acting by A_(g-inverse). -/
noncomputable def S2442MulAutEnd (g : Gv p) :
    MulAut (Multiplicative (muQZ p)) :=
  (S2442MuQZEndEquiv p g).toMultiplicative

/-- Value formula for the action automorphism. -/
@[simp]
theorem S2442MulAutEnd_apply (g : Gv p) (x : Multiplicative (muQZ p)) :
    S2442MulAutEnd p g x =
      Multiplicative.ofAdd (S2442MuQZEnd p g⁻¹ (Multiplicative.toAdd x)) :=
  rfl

/-- The group law of the honest action: g |-> A_(g-inverse) is multiplicative. -/
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
g-inverse. -/
theorem S2442MuQZAction_compat (g : Gv p) (H : Index p) (v : Stage p H) :
    Multiplicative.toAdd (S2442MuQZAction p g
        (Multiplicative.ofAdd (muQZof p H v))) =
      muQZof p (S2169ConjIndex p g⁻¹ H) (S2179StageConj p g⁻¹ H v) := by
  show Multiplicative.toAdd (S2442MulAutEnd p g
      (Multiplicative.ofAdd (muQZof p H v))) = _
  rw [S2442MulAutEnd_apply, toAdd_ofAdd]
  exact S2442MuQZEnd_muQZof p g⁻¹ H v

/-- The honest action inhabits the exact missing of S2159. -/
theorem S2442S2159MuQZActionRequired : S2159MuQZActionRequired p :=
  S2442MuQZAction p

/-! ## 7. The honest data structure and the literal S2189 structure -/

/-- The exact commutativity input which turns the anti-action into a genuine
g-indexed monoid hom: A_(g*h) = A_(h*g). -/
def S2442EndComm : Prop :=
  ∀ g h : Gv p, S2442MuQZEnd p (g * h) = S2442MuQZEnd p (h * g)

/-- The honest S2189-shaped data: the action g |-> A_(g-inverse) and its
g-inverse-indexed compatibility.  This is the corrected structure; its
action_compat is exactly S2442MuQZAction_compat. -/
structure S2442MuQZMulAutData where
  transfer_compat : S2179TransferCompatible (p := p)
  action : Gv p →* MulAut (Multiplicative (muQZ p))
  action_compat :
    ∀ (g : Gv p) (H : Index p) (v : Stage p H),
      Multiplicative.toAdd (action g (Multiplicative.ofAdd (muQZof p H v))) =
        muQZof p (S2169ConjIndex p g⁻¹ H) (S2179StageConj p g⁻¹ H v)

/-- Unconditional honest data. -/
noncomputable def S2442MuQZMulAutData_actual : S2442MuQZMulAutData p where
  transfer_compat := S2442_transferCompatible p
  action := S2442MuQZAction p
  action_compat := S2442MuQZAction_compat p

/-- The direct g-indexed additive equivalence, acting by A_g. -/
noncomputable def S2442MuQZEndEquivDirect (g : Gv p) : muQZ p ≃+ muQZ p where
  toFun := S2442MuQZEnd p g
  invFun := S2442MuQZEnd p g⁻¹
  left_inv x := by
    have h := DFunLike.congr_fun (S2442MuQZEnd_inv_comp p g) x
    simpa [AddMonoidHom.comp_apply] using h
  right_inv x := by
    have h := DFunLike.congr_fun (S2442MuQZEnd_comp_inv p g) x
    simpa [AddMonoidHom.comp_apply] using h
  map_add' := map_add _

/-- The direct g-indexed MulAut, acting by A_g. -/
noncomputable def S2442MulAutEndDirect (g : Gv p) :
    MulAut (Multiplicative (muQZ p)) :=
  (S2442MuQZEndEquivDirect p g).toMultiplicative

/-- Value formula for the direct action automorphism. -/
@[simp]
theorem S2442MulAutEndDirect_apply (g : Gv p) (x : Multiplicative (muQZ p)) :
    S2442MulAutEndDirect p g x =
      Multiplicative.ofAdd (S2442MuQZEnd p g (Multiplicative.toAdd x)) :=
  rfl

/-- Under S2442EndComm the direct action is a monoid hom. -/
noncomputable def S2442MuQZActionDirect (hcomm : S2442EndComm p) :
    Gv p →* MulAut (Multiplicative (muQZ p)) where
  toFun := S2442MulAutEndDirect p
  map_one' := by
    apply MulEquiv.ext
    intro x
    show Multiplicative.ofAdd (S2442MuQZEnd p 1 (Multiplicative.toAdd x)) = x
    rw [S2442MuQZEnd_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    rw [MulAut.mul_apply]
    show Multiplicative.ofAdd (S2442MuQZEnd p (g * h) (Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (S2442MuQZEnd p g
        (Multiplicative.toAdd (Multiplicative.ofAdd (S2442MuQZEnd p h (Multiplicative.toAdd x)))))
    rw [toAdd_ofAdd, hcomm g h, ← S2442MuQZEnd_comp]
    rfl

/-- The direct action satisfies the literal S2189 compatibility. -/
theorem S2442MuQZActionDirect_compat (hcomm : S2442EndComm p)
    (g : Gv p) (H : Index p) (v : Stage p H) :
    Multiplicative.toAdd (S2442MuQZActionDirect p hcomm g
        (Multiplicative.ofAdd (muQZof p H v))) =
      muQZof p (S2169ConjIndex p g H) (S2179StageConj p g H v) := by
  show Multiplicative.toAdd (S2442MulAutEndDirect p g
      (Multiplicative.ofAdd (muQZof p H v))) = _
  rw [S2442MulAutEndDirect_apply, toAdd_ofAdd]
  exact S2442MuQZEnd_muQZof p g H v

/-- Conditional construction of the literal S2189 data: the only extra input
beyond transfer compatibility is S2442EndComm. -/
noncomputable def S2442S2189MuQZMulAutDataOfComm (hcomm : S2442EndComm p) :
    S2189MuQZMulAutData p where
  transfer_compat := S2442_transferCompatible p
  action := S2442MuQZActionDirect p hcomm
  action_compat := S2442MuQZActionDirect_compat p hcomm

/-- The additive map underlying a MulAut of a Multiplicative type. -/
noncomputable def S2442AddOfMulAut (f : MulAut (Multiplicative (muQZ p))) :
    muQZ p →+ muQZ p where
  toFun x := Multiplicative.toAdd (f (Multiplicative.ofAdd x))
  map_zero' := by
    show Multiplicative.toAdd (f (Multiplicative.ofAdd (0 : muQZ p))) = 0
    rw [show Multiplicative.ofAdd (0 : muQZ p) = 1 from rfl, map_one]
    rfl
  map_add' x y := by
    show Multiplicative.toAdd (f (Multiplicative.ofAdd (x + y))) =
      Multiplicative.toAdd (f (Multiplicative.ofAdd x)) +
        Multiplicative.toAdd (f (Multiplicative.ofAdd y))
    rw [show Multiplicative.ofAdd (x + y) =
      Multiplicative.ofAdd x * Multiplicative.ofAdd y from rfl, map_mul]
    rfl

/-- Value formula for S2442AddOfMulAut. -/
@[simp]
theorem S2442AddOfMulAut_apply (f : MulAut (Multiplicative (muQZ p))) (x : muQZ p) :
    S2442AddOfMulAut p f x = Multiplicative.toAdd (f (Multiplicative.ofAdd x)) :=
  rfl

/-- Its values on generators are exactly the stage conjugation, hence it is
A_g by uniqueness of the colimit map. -/
theorem S2442AddOfMulAut_eq (D : S2189MuQZMulAutData p) (g : Gv p) :
    S2442AddOfMulAut p (S2189MuQZMulAutData.action D g) = S2442MuQZEnd p g := by
  apply muQZ_lift_unique p (muQZ p) (S2442MuQZEndFamily p g)
    (S2442MuQZEndFamily_compat p g)
  intro H v
  rw [S2442AddOfMulAut_apply]
  change Multiplicative.toAdd
      (S2189MuQZMulAutData.action D g (Multiplicative.ofAdd (muQZof p H v))) =
    S2442MuQZEndFamily p g H v
  rw [S2189MuQZMulAutData.action_compat D g H v]
  rfl

/-- The literal S2189 data forces the commutativity input: any
S2189MuQZMulAutData yields S2442EndComm. -/
theorem S2442EndComm_of_s2189 (D : S2189MuQZMulAutData p) : S2442EndComm p := by
  intro g h
  have hlaw := map_mul (S2189MuQZMulAutData.action D) g h
  have h1 : S2442AddOfMulAut p (S2189MuQZMulAutData.action D (g * h)) =
      (S2442AddOfMulAut p (S2189MuQZMulAutData.action D g)).comp
        (S2442AddOfMulAut p (S2189MuQZMulAutData.action D h)) := by
    rw [hlaw]
    rfl
  rw [S2442AddOfMulAut_eq p D (g * h), S2442AddOfMulAut_eq p D g,
    S2442AddOfMulAut_eq p D h] at h1
  rw [h1, S2442MuQZEnd_comp]

#check S2442_transferCompatible
#check S2442MuQZEnd
#check S2442MuQZEnd_muQZof
#check S2442ConjIndex_comp
#check S2442_stageConj_comp
#check S2442MuQZEnd_comp
#check S2442MuQZEnd_one
#check S2442MuQZEnd_comp_inv
#check S2442MuQZEnd_inv_comp
#check S2442MuQZAction
#check S2442MuQZAction_compat
#check S2442MuQZMulAutData
#check S2442MuQZMulAutData_actual
#check S2442S2189MuQZMulAutDataOfComm
#check S2442EndComm_of_s2189

#print axioms S2442_transferCompatible
#print axioms S2442MuQZEnd
#print axioms S2442MuQZEnd_muQZof
#print axioms S2442ConjIndex_comp
#print axioms S2442_stageConj_comp
#print axioms S2442MuQZEnd_comp
#print axioms S2442MuQZEnd_one
#print axioms S2442MuQZEnd_comp_inv
#print axioms S2442MuQZEnd_inv_comp
#print axioms S2442MulAutEnd_mul
#print axioms S2442MuQZAction
#print axioms S2442MuQZAction_compat
#print axioms S2442MuQZMulAutData_actual
#print axioms S2442S2189MuQZMulAutDataOfComm
#print axioms S2442EndComm_of_s2189

end LeanFormal.IUT.XiFPaper.S2442MulAutDataSubagentActual

end
