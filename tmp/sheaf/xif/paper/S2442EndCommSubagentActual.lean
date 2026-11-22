import tmp.sheaf.xif.paper.S2430TorsionDescentSubagentActual
import tmp.sheaf.xif.paper.S2189TransferCompatActual
import tmp.sheaf.xif.paper.S2317SubgroupOfApplyActual
import tmp.sheaf.xif.paper.S2200TransferNaturalityActual
import tmp.sheaf.xif.paper.S2173StageConjugationActual
import tmp.sheaf.xif.paper.S2169MuQZConjugationActual
import tmp.sheaf.xif.paper.S2017VerlagerungActual

/-!
# S2442: the anti-hom algebra of the stage-conjugation action on muQZ, and EndComm

Layer: O (Theta-link / q-pilot).  Independent file: the unfinished
S2431MuQZMulAutSubagentActual.lean (compile errors + sorryAx upstream) is not
imported and not used as an interface; the inputs are the clean chain S2017
(muQZ colimit), S2169 (conjugation index), S2179/S2200/S2317 (stage
conjugation and its abelianization coefficient), S2371/S2300 (transfer
naturality) and S2430 (transfer compatibility, fully proved).

## The question

For g : Gv p let A_g : muQZ p -> muQZ p be the additive endomorphism induced
(through muQZ_lift) by the stage conjugation
S2179StageConj g H : Stage p H ≃+ Stage p (S2169ConjIndex g H), where
S2169ConjIndex g H = H.comap (conj g) is g⁻¹Hg and S2179StageConj g H is the
torsion of the abelianization of x ↦ g⁻¹xg on H.

S2431EndComm (the S2189/S2431 interface) asks

  A_(g*h) = A_(h*g)  for all g h : Gv p.

## What is proved here

* S2442MuQZEnd, S2442MuQZEnd_muQZof: the endomorphism and its computation rule
  on the colimit generators.
* S2442MuQZEnd_comp: the ANTI-HOM LAW A_g o A_h = A_(h*g).  This is the actual
  group law of the construction: the stage conjugation acts by x ↦ g⁻¹xg, so
  the subgroup index composes as g⁻¹(h⁻¹Hh)g = (hg)⁻¹H(hg).  The honest
  g-indexed object is therefore an anti-hom, not a hom.
* S2442MuQZEnd_one, S2442MuQZEnd_comp_inv, S2442MuQZEnd_inv_comp: each A_g is
  an additive equivalence with inverse A_(g⁻¹).
* S2442EndComm: the commutativity input, with the chain of equivalences
  - S2442EndComm_iff_pairwise: EndComm ↔ ∀ g h, A_g o A_h = A_h o A_g
    (the image of the anti-hom action is commutative);
  - S2442MuQZEnd_commutator: the exact commutator identity
    A_⁅g,h⁆ = A_((hg)⁻¹) o A_(gh), hence S2442EndComm_iff_commutator:
    EndComm ↔ A kills every commutator ⁅g,h⁆, i.e. the anti-hom action
    factors through the commutator subgroup;
  - S2442EndComm_iff_direct_hom: EndComm is exactly the statement that the
    g-indexed direct action g ↦ A_g is a monoid hom;
  - S2442EndComm_iff_s2189: EndComm ↔ Nonempty (S2189MuQZMulAutData p).
* S2442MulAutEndHonest, S2442MuQZAction: the HONEST monoid hom g ↦ A_(g⁻¹),
  which exists unconditionally, together with the g⁻¹-indexed compatibility
  S2442MuQZAction_compat.  This is the anti-hom-corrected form of the S2189
  action field.
* S2442CyclotomicScalarRequired, S2442EndComm_of_cyclotomicScalar: the precise
  sufficient algebraic input, of cyclotomic shape: a commutative ring of
  scalars R, a Module R (muQZ p), a monoid hom χ : Gv p →* R, and
  A_g x = χ g • x.  Then A_g A_h = χ g • χ h • x = χ h • χ g • x.
* Honest partial results: S2442EndComm_of_subsingleton (the tree does not prove
  muQZ p is nontrivial, so EndComm is not refutable from it either) and
  S2442EndComm_of_commutative.

## Status of S2431EndComm

EndComm is NOT proved here and is NOT a formal consequence of the
transfer-colimit construction: that construction produces the anti-hom g ↦ A_g
for every coefficient system, and the commutator identity above shows that
EndComm is precisely the extra statement that the commutator subgroup of Gv p
acts trivially on the cyclotome.  The exact first missing algebraic input is
recorded as S2442CyclotomicScalarRequired; the arithmetic instance (local
reciprocity (M2a)/(M2c) of S2027 together with the cyclotomic character acting
on the mu-side, i.e. the cyclotomic description of muQZ p as Q/Z, whose
endomorphism monoid is commutative) is not available in this tree, so no claim
about S2189 data being actual is made.

## Not run

Full Project build, target comparator, independent review.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open scoped commutatorElement

namespace LeanFormal.IUT.XiFPaper.S2442EndCommSubagentActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2317SubgroupOfApplyActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2371HnatExplicitActual
open LeanFormal.IUT.XiFPaper.S2430TorsionDescentSubagentActual
open LeanFormal.IUT.XiFPaper.S2189TransferCompatActual

universe u

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. Conjugation of open subgroups -/

/-- Conjugating twice composes the open subgroups:
conj_g (conj_h H) = conj_(h*g) H for the index S2169ConjIndex g H = g⁻¹Hg. -/
theorem S2442_conjIndex_comp (g h : Gv p) (H : Index p) :
    S2169ConjIndex p g (S2169ConjIndex p h H) = S2169ConjIndex p (h * g) H := by
  apply OpenSubgroup.ext
  intro x
  simp only [S2169ConjIndex, OpenSubgroup.mem_comap]
  have hlhs : (MulAut.conj h).toMonoidHom ((MulAut.conj g).toMonoidHom x)
      = h * g * x * (h * g)⁻¹ := by
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MulAut.conj_apply]
    group
  have hrhs : (MulAut.conj (h * g)).toMonoidHom x = h * g * x * (h * g)⁻¹ := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hlhs, hrhs]

/-- Conjugation by 1 is the identity on open subgroups. -/
theorem S2442_conjIndex_one (H : Index p) : S2169ConjIndex p 1 H = H := by
  apply OpenSubgroup.ext
  intro x
  simp only [S2169ConjIndex, OpenSubgroup.mem_comap]
  have h : (MulAut.conj (1 : Gv p)).toMonoidHom x = x := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp
  rw [h]

/-- muQZof is invariant under an equality of open subgroups. -/
theorem S2442_muQZof_cast {H H' : Index p} (e : H = H') (v : Stage p H) :
    muQZof p H v = muQZof p H' (e ▸ v) := by
  cases e
  rfl

/-! ## 2. Functoriality of the abelianization and torsion coefficients -/

/-- The abelianization equivalence on a generator. -/
theorem S2442_abelianizationCongr_of {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    abelianizationCongr e (Abelianization.of x) = Abelianization.of (e x) := rfl

/-- The abelianization equivalence of a composite is the composite. -/
theorem S2442_abelianizationCongr_trans {G H I : Type u} [Group G] [Group H] [Group I]
    (e₁ : G ≃* H) (e₂ : H ≃* I) :
    abelianizationCongr (e₁.trans e₂) =
      (abelianizationCongr e₁).trans (abelianizationCongr e₂) := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
    S2442_abelianizationCongr_of]

/-- The abelianization of the identity is the identity. -/
theorem S2442_abelianizationCongr_refl {G : Type u} [Group G] :
    abelianizationCongr (MulEquiv.refl G) = MulEquiv.refl (Abelianization G) := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    S2442_abelianizationCongr_of, MulEquiv.refl_apply]

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
  apply Subtype.ext
  simp only [S2430_torsionCongr_coe]
  rw [S2442_abelianizationCongr_trans]
  rfl

/-- Casting a torsion value along an equality of open subgroups, controlled by
the underlying element maps of the two subgroup coefficients. -/
theorem S2442_stageCongr_index_cast_apply {H A B : Index p}
    (e : A = B) (eA : ↥H ≃* ↥A) (eB : ↥H ≃* ↥B)
    (h : ∀ x : ↥H, ((eA x : ↥A) : Gv p) = ((eB x : ↥B) : Gv p))
    (w : CommGroup.torsion (Abelianization ↥H)) :
    e ▸ (Additive.ofMul (torsionCongr (abelianizationCongr eA) w)) =
      Additive.ofMul (torsionCongr (abelianizationCongr eB) w) := by
  cases e
  have he : eA = eB := MulEquiv.ext (fun x => Subtype.ext (h x))
  rw [he]

/-! ## 3. Composition of the actual stage conjugations -/

/-- Composition of the actual stage conjugations, with the open-subgroup
equality made explicit. -/
theorem S2442_stageConj_comp (g h : Gv p) (H : Index p) (v : Stage p H) :
    (S2442_conjIndex_comp p g h H) ▸
        (S2179StageConj p g (S2169ConjIndex p h H)
          (S2179StageConj p h H v)) =
      S2179StageConj p (h * g) H v := by
  have hv : v = Additive.ofMul (Additive.toMul v) := rfl
  rw [hv]
  simp only [S2430_stageConj_apply]
  rw [S2442_stageCongr_trans_apply (e₁ := S2200ConjEquiv p h H)
    (e₂ := S2200ConjEquiv p g (S2169ConjIndex p h H))]
  exact S2442_stageCongr_index_cast_apply
    (H := H)
    (A := S2169ConjIndex p g (S2169ConjIndex p h H))
    (B := S2169ConjIndex p (h * g) H)
    (e := S2442_conjIndex_comp p g h H)
    (eA := (S2200ConjEquiv p h H).trans (S2200ConjEquiv p g (S2169ConjIndex p h H)))
    (eB := S2200ConjEquiv p (h * g) H)
    (by
      intro x
      simp only [MulEquiv.trans_apply, S2317ConjEquiv_apply]
      group)
    (Additive.toMul v)

/-- The stage conjugation by 1 is the identity, after the subgroup equality. -/
theorem S2442_stageConj_one_apply (H : Index p)
    (w : CommGroup.torsion (Abelianization ↥H)) :
    (S2442_conjIndex_one p H) ▸ (S2179StageConj p 1 H (Additive.ofMul w)) =
      Additive.ofMul w := by
  rw [S2430_stageConj_apply]
  refine (S2442_stageCongr_index_cast_apply (H := H)
    (A := S2169ConjIndex p 1 H) (B := H)
    (S2442_conjIndex_one p H) (S2200ConjEquiv p 1 H) (MulEquiv.refl ↥H)
    (by intro x; rw [S2317ConjEquiv_apply]; simp) w).trans ?_
  rw [S2442_abelianizationCongr_refl, S2442_torsionCongr_refl]
  rfl

/-! ## 4. The additive endomorphism attached to g -/

/-- The levelwise family defining the endomorphism of muQZ p attached to
g : Gv p. -/
noncomputable def S2442MuQZEndFamily (g : Gv p) :
    ∀ H : Index p, Stage p H →+ muQZ p :=
  fun H => (muQZof p (S2169ConjIndex p g H)).comp (S2179StageConj p g H).toAddMonoidHom

/-- The compatibility with the transfer maps, from transfer compatibility. -/
theorem S2442MuQZEndFamily_compat (g : Gv p) :
    ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      S2442MuQZEndFamily p g H (toStage p h v) =
        S2442MuQZEndFamily p g K v := by
  intro H K h v
  obtain ⟨h', hEq⟩ := S2430_transferCompatible (p := p) g H K h v
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

/-! ## 5. The anti-hom law and the inverse -/

/-- ANTI-HOM LAW: A_g o A_h = A_(h*g). -/
theorem S2442MuQZEnd_comp (g h : Gv p) :
    (S2442MuQZEnd p g).comp (S2442MuQZEnd p h) = S2442MuQZEnd p (h * g) := by
  refine muQZ_lift_unique p (muQZ p) (S2442MuQZEndFamily p (h * g))
    (S2442MuQZEndFamily_compat p (h * g))
    ((S2442MuQZEnd p g).comp (S2442MuQZEnd p h)) ?_
  intro H v
  rw [AddMonoidHom.comp_apply, S2442MuQZEnd_muQZof, S2442MuQZEnd_muQZof]
  exact (S2442_muQZof_cast (e := S2442_conjIndex_comp p g h H)
      (v := S2179StageConj p g (S2169ConjIndex p h H)
        (S2179StageConj p h H v))).trans
    (congrArg (muQZof p (S2169ConjIndex p (h * g) H))
      (S2442_stageConj_comp p g h H v))

/-- The endomorphism attached to 1 is the identity. -/
theorem S2442MuQZEnd_one : S2442MuQZEnd p 1 = AddMonoidHom.id (muQZ p) := by
  have hcomp : ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      muQZof p H (toStage p h v) = muQZof p K v :=
    fun {H K} h v => muQZof_transfer (p := p) h v
  have h1 := muQZ_lift_unique p (muQZ p) (fun H : Index p => muQZof p H) hcomp
    (S2442MuQZEnd p 1) (by
      intro H v
      rw [S2442MuQZEnd_muQZof]
      have hv : v = Additive.ofMul (Additive.toMul v) := rfl
      rw [hv]
      exact (S2442_muQZof_cast (e := S2442_conjIndex_one p H)
          (v := S2179StageConj p 1 H
            (Additive.ofMul (Additive.toMul v)))).trans
        (congrArg (muQZof p H) (S2442_stageConj_one_apply p H (Additive.toMul v))))
  have h2 := muQZ_lift_unique p (muQZ p) (fun H : Index p => muQZof p H) hcomp
    (AddMonoidHom.id (muQZ p)) (fun H v => rfl)
  exact h1.trans h2.symm

/-- Inverse law, one order. -/
theorem S2442MuQZEnd_comp_inv (g : Gv p) :
    (S2442MuQZEnd p g).comp (S2442MuQZEnd p (g⁻¹)) = AddMonoidHom.id (muQZ p) := by
  rw [S2442MuQZEnd_comp, inv_mul_cancel]
  exact S2442MuQZEnd_one p

/-- Inverse law, the other order. -/
theorem S2442MuQZEnd_inv_comp (g : Gv p) :
    (S2442MuQZEnd p (g⁻¹)).comp (S2442MuQZEnd p g) = AddMonoidHom.id (muQZ p) := by
  rw [S2442MuQZEnd_comp, mul_inv_cancel]
  exact S2442MuQZEnd_one p

/-! ## 6. The commutator identity and EndComm -/

/-- The exact commutator identity for the anti-hom action:
A_⁅g,h⁆ = A_((h*g)⁻¹) o A_(g*h). -/
theorem S2442MuQZEnd_commutator (g h : Gv p) :
    S2442MuQZEnd p ⁅g, h⁆ =
      (S2442MuQZEnd p ((h * g)⁻¹)).comp (S2442MuQZEnd p (g * h)) := by
  have hkey : (g * h) * (h * g)⁻¹ = ⁅g, h⁆ := by
    rw [commutatorElement_def, mul_inv_rev]
    group
  rw [← hkey]
  exact (S2442MuQZEnd_comp p ((h * g)⁻¹) (g * h)).symm

/-- The commutativity input of the S2431/S2189 interface:
A_(g*h) = A_(h*g) for all g h. -/
def S2442EndComm : Prop :=
  ∀ g h : Gv p, S2442MuQZEnd p (g * h) = S2442MuQZEnd p (h * g)

/-- EndComm is precisely the commutativity of the image of the anti-hom. -/
theorem S2442EndComm_iff_pairwise :
    S2442EndComm p ↔ ∀ g h : Gv p,
      (S2442MuQZEnd p g).comp (S2442MuQZEnd p h) =
        (S2442MuQZEnd p h).comp (S2442MuQZEnd p g) := by
  constructor
  · intro hc g h
    rw [S2442MuQZEnd_comp, S2442MuQZEnd_comp, hc g h]
  · intro hp g h
    have h1 := hp g h
    rw [S2442MuQZEnd_comp, S2442MuQZEnd_comp] at h1
    exact h1.symm

/-- The exact first missing in group-theoretic form: every commutator acts
trivially on muQZ p. -/
def S2442CommutatorTrivial : Prop :=
  ∀ g h : Gv p, S2442MuQZEnd p ⁅g, h⁆ = AddMonoidHom.id (muQZ p)

/-- EndComm is equivalent to the triviality of the anti-hom action on the
commutator subgroup, i.e. to factorization through Gv p modulo its commutator
subgroup. -/
theorem S2442EndComm_iff_commutator :
    S2442EndComm p ↔ S2442CommutatorTrivial p := by
  constructor
  · intro hc g h
    rw [S2442MuQZEnd_commutator, hc g h]
    exact S2442MuQZEnd_comp_inv p (h * g)
  · intro hk g h
    apply AddMonoidHom.ext
    intro x
    have h1 : (S2442MuQZEnd p ((h * g)⁻¹)) ((S2442MuQZEnd p (g * h)) x) = x := by
      have hh := DFunLike.congr_fun (hk g h) x
      rw [S2442MuQZEnd_commutator] at hh
      simpa [AddMonoidHom.comp_apply] using hh
    have h2 := congrArg (fun y => (S2442MuQZEnd p (h * g)) y) h1
    have h3 : (S2442MuQZEnd p (h * g))
        ((S2442MuQZEnd p ((h * g)⁻¹)) ((S2442MuQZEnd p (g * h)) x)) =
        (S2442MuQZEnd p (g * h)) x := by
      have hh := DFunLike.congr_fun (S2442MuQZEnd_comp_inv p (h * g))
        ((S2442MuQZEnd p (g * h)) x)
      simpa [AddMonoidHom.comp_apply] using hh
    rw [h3] at h2
    exact h2

/-- The g-indexed direct additive equivalence attached to A_g. -/
noncomputable def S2442MuQZEndEquivDirect (g : Gv p) : muQZ p ≃+ muQZ p where
  toFun := S2442MuQZEnd p g
  invFun := S2442MuQZEnd p (g⁻¹)
  left_inv x := by
    have h := DFunLike.congr_fun (S2442MuQZEnd_inv_comp p g) x
    simpa [AddMonoidHom.comp_apply] using h
  right_inv x := by
    have h := DFunLike.congr_fun (S2442MuQZEnd_comp_inv p g) x
    simpa [AddMonoidHom.comp_apply] using h
  map_add' := map_add _

/-- The g-indexed direct MulAut, acting by A_g. -/
noncomputable def S2442MulAutEndDirect (g : Gv p) :
    MulAut (Multiplicative (muQZ p)) :=
  (S2442MuQZEndEquivDirect p g).toMultiplicative

/-- Value formula for the direct action. -/
theorem S2442MulAutEndDirect_apply (g : Gv p) (x : Multiplicative (muQZ p)) :
    S2442MulAutEndDirect p g x =
      Multiplicative.ofAdd (S2442MuQZEnd p g (Multiplicative.toAdd x)) := rfl

/-- EndComm is exactly the statement that the direct action is a monoid hom:
the anti-hom law makes A_g o A_h = A_(h*g). -/
theorem S2442EndComm_iff_direct_hom :
    S2442EndComm p ↔ ∀ g h : Gv p,
      S2442MulAutEndDirect p (g * h) =
        S2442MulAutEndDirect p g * S2442MulAutEndDirect p h := by
  constructor
  · intro hc g h
    apply MulEquiv.ext
    intro x
    rw [MulAut.mul_apply]
    show Multiplicative.ofAdd (S2442MuQZEnd p (g * h) (Multiplicative.toAdd x)) =
      S2442MulAutEndDirect p g (S2442MulAutEndDirect p h x)
    rw [S2442MulAutEndDirect_apply, S2442MulAutEndDirect_apply]
    simp only [toAdd_ofAdd]
    rw [hc g h]
    have hcomp := DFunLike.congr_fun (S2442MuQZEnd_comp p g h)
      (Multiplicative.toAdd x)
    simp only [AddMonoidHom.comp_apply] at hcomp
    rw [hcomp]
  · intro hh g h
    apply AddMonoidHom.ext
    intro x
    have h1 := DFunLike.congr_fun (hh g h) (Multiplicative.ofAdd x)
    rw [MulAut.mul_apply] at h1
    simp only [S2442MulAutEndDirect_apply, toAdd_ofAdd] at h1
    have h2 := DFunLike.congr_fun (S2442MuQZEnd_comp p g h) x
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2] at h1
    exact Multiplicative.ofAdd.injective h1

/-! ## 7. The honest g⁻¹-indexed action -/

/-- The additive equivalence x ↦ A_(g⁻¹) x. -/
noncomputable def S2442MuQZEndEquivHonest (g : Gv p) : muQZ p ≃+ muQZ p where
  toFun := S2442MuQZEnd p (g⁻¹)
  invFun := S2442MuQZEnd p g
  left_inv x := by
    have h := DFunLike.congr_fun (S2442MuQZEnd_comp_inv p g) x
    simpa [AddMonoidHom.comp_apply] using h
  right_inv x := by
    have h := DFunLike.congr_fun (S2442MuQZEnd_inv_comp p g) x
    simpa [AddMonoidHom.comp_apply] using h
  map_add' := map_add _

/-- The honest MulAut attached to g, acting by A_(g⁻¹). -/
noncomputable def S2442MulAutEndHonest (g : Gv p) :
    MulAut (Multiplicative (muQZ p)) :=
  (S2442MuQZEndEquivHonest p g).toMultiplicative

/-- Value formula for the honest action. -/
theorem S2442MulAutEndHonest_apply (g : Gv p) (x : Multiplicative (muQZ p)) :
    S2442MulAutEndHonest p g x =
      Multiplicative.ofAdd (S2442MuQZEnd p (g⁻¹) (Multiplicative.toAdd x)) := rfl

/-- The honest action is a monoid hom, unconditionally. -/
theorem S2442MulAutEndHonest_mul (g h : Gv p) :
    S2442MulAutEndHonest p (g * h) =
      S2442MulAutEndHonest p g * S2442MulAutEndHonest p h := by
  apply MulEquiv.ext
  intro x
  rw [MulAut.mul_apply]
  show Multiplicative.ofAdd (S2442MuQZEnd p ((g * h)⁻¹) (Multiplicative.toAdd x)) =
    S2442MulAutEndHonest p g (S2442MulAutEndHonest p h x)
  rw [S2442MulAutEndHonest_apply, S2442MulAutEndHonest_apply]
  simp only [toAdd_ofAdd, mul_inv_rev]
  exact congrArg Multiplicative.ofAdd
    (DFunLike.congr_fun (S2442MuQZEnd_comp p (g⁻¹) (h⁻¹))
      (Multiplicative.toAdd x)).symm

/-- The honest monoid hom Gv p →* MulAut (Multiplicative (muQZ p)), g ↦ A_(g⁻¹). -/
noncomputable def S2442MuQZAction :
    Gv p →* MulAut (Multiplicative (muQZ p)) where
  toFun := S2442MulAutEndHonest p
  map_one' := by
    apply MulEquiv.ext
    intro x
    show Multiplicative.ofAdd (S2442MuQZEnd p (1⁻¹) (Multiplicative.toAdd x)) = x
    rw [inv_one, S2442MuQZEnd_one]
    exact ofAdd_toAdd x
  map_mul' := S2442MulAutEndHonest_mul p

/-- The honest g⁻¹-indexed compatibility: the action by g is the stage
conjugation with g⁻¹. -/
theorem S2442MuQZAction_compat (g : Gv p) (H : Index p) (v : Stage p H) :
    Multiplicative.toAdd (S2442MuQZAction p g
        (Multiplicative.ofAdd (muQZof p H v))) =
      muQZof p (S2169ConjIndex p (g⁻¹) H) (S2179StageConj p (g⁻¹) H v) := by
  show Multiplicative.toAdd (S2442MulAutEndHonest p g
      (Multiplicative.ofAdd (muQZof p H v))) = _
  rw [S2442MulAutEndHonest_apply]
  simp only [toAdd_ofAdd]
  exact S2442MuQZEnd_muQZof p (g⁻¹) H v

/-! ## 8. The literal S2189 structure is equivalent to EndComm -/

/-- Conditional construction of the literal S2189MuQZMulAutData: the honest
g⁻¹-indexed action always exists, while the g-indexed field is exactly
EndComm. -/
noncomputable def S2442S2189Data_of_EndComm (hc : S2442EndComm p) :
    S2189MuQZMulAutData p where
  transfer_compat := S2430_transferCompatible p
  action :=
    { toFun := S2442MulAutEndDirect p
      map_one' := by
        apply MulEquiv.ext
        intro x
        show Multiplicative.ofAdd (S2442MuQZEnd p 1 (Multiplicative.toAdd x)) = x
        rw [S2442MuQZEnd_one]
        exact ofAdd_toAdd x
      map_mul' := (S2442EndComm_iff_direct_hom p).mp hc }
  action_compat := by
    intro g H v
    show Multiplicative.toAdd (S2442MulAutEndDirect p g
      (Multiplicative.ofAdd (muQZof p H v))) = _
    rw [S2442MulAutEndDirect_apply]
    simp only [toAdd_ofAdd]
    exact S2442MuQZEnd_muQZof p g H v

/-- The additive map underlying a MulAut of Multiplicative (muQZ p). -/
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
theorem S2442AddOfMulAut_apply (f : MulAut (Multiplicative (muQZ p))) (x : muQZ p) :
    S2442AddOfMulAut p f x = Multiplicative.toAdd (f (Multiplicative.ofAdd x)) := rfl

/-- The additive map of an S2189 action is A_g on the colimit generators, hence
equal to A_g by the universal property. -/
theorem S2442AddOfMulAut_eq (D : S2189MuQZMulAutData p) (g : Gv p) :
    S2442AddOfMulAut p (S2189MuQZMulAutData.action D g) = S2442MuQZEnd p g := by
  refine muQZ_lift_unique p (muQZ p) (S2442MuQZEndFamily p g)
    (S2442MuQZEndFamily_compat p g) _ ?_
  intro H v
  rw [S2442AddOfMulAut_apply]
  show Multiplicative.toAdd
      (S2189MuQZMulAutData.action D g (Multiplicative.ofAdd (muQZof p H v))) =
    S2442MuQZEndFamily p g H v
  rw [S2189MuQZMulAutData.action_compat D g H v]
  rfl

/-- The literal S2189 data forces EndComm. -/
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

/-- The literal S2189 structure exists if and only if EndComm holds. -/
theorem S2442EndComm_iff_s2189 :
    S2442EndComm p ↔ Nonempty (S2189MuQZMulAutData p) :=
  ⟨fun h => ⟨S2442S2189Data_of_EndComm p h⟩, fun ⟨D⟩ => S2442EndComm_of_s2189 p D⟩

/-! ## 9. The sufficient algebraic input of cyclotomic type -/

/-- The cyclotomic scalar input: the action is scalar multiplication from a
commutative ring, along a multiplicative character.  In the arithmetic instance
R is (a subring of) Z_p, chi is the cyclotomic character and the module
structure is the action on mu_{Q/Z}. -/
def S2442CyclotomicScalarRequired : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : Module R (muQZ p)) (χ : Gv p →* R),
    ∀ (g : Gv p) (x : muQZ p), S2442MuQZEnd p g x = χ g • x

/-- The cyclotomic scalar input implies EndComm: scalar multiplications from a
commutative ring commute. -/
theorem S2442EndComm_of_cyclotomicScalar
    (h : S2442CyclotomicScalarRequired p) : S2442EndComm p := by
  obtain ⟨R, hR, hM, χ, hχ⟩ := h
  letI := hR
  letI := hM
  refine (S2442EndComm_iff_pairwise p).mpr ?_
  intro g h'
  apply AddMonoidHom.ext
  intro x
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  simp only [hχ, smul_smul, mul_comm]

/-! ## 10. Honest partial results and the logical position of EndComm -/

/-- EndComm holds in the trivial case: the tree does not prove that muQZ p is
nontrivial, so EndComm is not refutable from the tree either. -/
theorem S2442EndComm_of_subsingleton [Subsingleton (muQZ p)] : S2442EndComm p := by
  intro g h
  exact AddMonoidHom.ext (fun x => Subsingleton.elim _ _)

/-- EndComm holds whenever Gv p is commutative: the obstruction is exactly the
commutator subgroup, as also visible from S2442EndComm_iff_commutator. -/
theorem S2442EndComm_of_commutative (hc : ∀ g h : Gv p, g * h = h * g) :
    S2442EndComm p := by
  intro g h
  rw [hc g h]

#check S2442_conjIndex_comp
#check S2442_stageConj_comp
#check S2442MuQZEnd
#check S2442MuQZEnd_muQZof
#check S2442MuQZEnd_comp
#check S2442MuQZEnd_one
#check S2442MuQZEnd_comp_inv
#check S2442MuQZEnd_inv_comp
#check S2442MuQZEnd_commutator
#check S2442EndComm
#check S2442EndComm_iff_pairwise
#check S2442CommutatorTrivial
#check S2442EndComm_iff_commutator
#check S2442MulAutEndDirect
#check S2442EndComm_iff_direct_hom
#check S2442MulAutEndHonest
#check S2442MuQZAction
#check S2442MuQZAction_compat
#check S2442S2189Data_of_EndComm
#check S2442EndComm_of_s2189
#check S2442EndComm_iff_s2189
#check S2442CyclotomicScalarRequired
#check S2442EndComm_of_cyclotomicScalar
#check S2442EndComm_of_subsingleton
#check S2442EndComm_of_commutative

#print axioms S2442_conjIndex_comp
#print axioms S2442_conjIndex_one
#print axioms S2442_muQZof_cast
#print axioms S2442_abelianizationCongr_trans
#print axioms S2442_stageCongr_trans_apply
#print axioms S2442_stageCongr_index_cast_apply
#print axioms S2442_stageConj_comp
#print axioms S2442_stageConj_one_apply
#print axioms S2442MuQZEnd
#print axioms S2442MuQZEnd_muQZof
#print axioms S2442MuQZEnd_comp
#print axioms S2442MuQZEnd_one
#print axioms S2442MuQZEnd_comp_inv
#print axioms S2442MuQZEnd_inv_comp
#print axioms S2442MuQZEnd_commutator
#print axioms S2442EndComm_iff_pairwise
#print axioms S2442EndComm_iff_commutator
#print axioms S2442EndComm_iff_direct_hom
#print axioms S2442MulAutEndHonest_mul
#print axioms S2442MuQZAction
#print axioms S2442MuQZAction_compat
#print axioms S2442S2189Data_of_EndComm
#print axioms S2442EndComm_of_s2189
#print axioms S2442EndComm_iff_s2189
#print axioms S2442EndComm_of_cyclotomicScalar

end LeanFormal.IUT.XiFPaper.S2442EndCommSubagentActual

end
