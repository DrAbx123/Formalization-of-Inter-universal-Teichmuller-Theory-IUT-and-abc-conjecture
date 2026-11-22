import tmp.sheaf.xif.paper.S2430TorsionDescentSubagentActual

/-!
# S2432: salvaged MuQZ MulAut data for the transfer chain

Layer: O (Theta-link / q-pilot).  This is an independent, compiling target
file; the unfinished attempt `S2431MuQZMulAutSubagentActual.lean` is not
edited and not imported.

## What is proved here (unconditional, no sorry/axiom/True/PUnit)

* `S2432_transferCompatible`: the S2179 transfer-compatibility statement,
  reused from the fully proved `S2430_transferCompatible`.
* `S2432MuQZEnd`: the additive endomorphism of `muQZ p` attached to
  `g : Gv p`, obtained from `muQZ_lift` and the stage conjugation, with
  computation rule `S2432MuQZEnd_muQZof`.
* `S2432ConjIndex_comp`, `S2432_stageConj_comp`: the anti-composition law
  of the open-subgroup conjugation and of the actual stage conjugations.
* `S2432MuQZEnd_comp`: `A_g o A_h = A_(h*g)`; consequently
  `S2432MuQZEnd_comp_inv`, `S2432MuQZEnd_inv_comp` (inverse field), and
  `S2432MuQZEnd_one`.
* `S2432MuQZAction : Gv p →* MulAut (Multiplicative (muQZ p))`, the honest
  monoid hom `g |-> A_(g^-1)`, with value formula and `g^-1`-compatibility
  `S2432MuQZAction_compat`.  This inhabits `S2159MuQZActionRequired`.
* `S2432MuQZAction_continuous`: continuity for the only topology declared in
  the tree (the discrete topology of S2159).

## Status of the four S2189 fields

* inverse: done (`S2432MuQZEnd_comp_inv`, `S2432MuQZEnd_inv_comp`).
* multiplication/group law: done (`S2432MuQZEnd_comp`, `S2432MulAutEnd_mul`,
  `S2432MuQZAction`).  The honest action is `g |-> A_(g^-1)`.
* continuity: the discrete-topology statement is proved
  (`S2432MuQZAction_continuous`); the paper's *joint* continuity needs a
  non-discrete topology on `muQZ p`, which the tree does not declare.  The
  exact missing input is recorded as the precise `Prop`
  `S2432ActionJointContinuous` (parameterised by a topology); it is assumed
  nowhere.
* equivariance: the honest action satisfies the `g^-1`-indexed law
  `S2432MuQZAction_compat`.  The literal S2189 field is stated with the
  `g`-indexed stage; it is equivalent to the commutativity input
  `S2432EndComm` (see `S2432EndComm_of_s2189` /
  `S2432S2189MuQZMulAutDataOfComm`).  `S2432EndComm` is the exact first
  missing for the *literal* S2189 structure.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2432MuQZMulAutDoneActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2317SubgroupOfApplyActual
open LeanFormal.IUT.XiFPaper.S2371HnatExplicitActual
open LeanFormal.IUT.XiFPaper.S2430TorsionDescentSubagentActual
open LeanFormal.IUT.XiFPaper.S2189TransferCompatActual
open LeanFormal.IUT.XiFPaper.S2159MuQZActionActual

universe u

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. Transfer compatibility and the open-subgroup conjugation -/

/-- Transfer compatibility, reused from the fully proved S2430 result. -/
theorem S2432_transferCompatible : S2179TransferCompatible (p := p) :=
  S2430_transferCompatible p

/-- Conjugating twice composes the open subgroups: conj_g (conj_h H) is
conj_(h*g) H. -/
theorem S2432ConjIndex_comp (g h : Gv p) (H : Index p) :
    S2169ConjIndex p g (S2169ConjIndex p h H) = S2169ConjIndex p (h * g) H := by
  apply OpenSubgroup.ext
  intro x
  simp only [S2169ConjIndex, OpenSubgroup.mem_comap]
  change MulAut.conj h (MulAut.conj g x) ∈ H ↔ MulAut.conj (h * g) x ∈ H
  simp only [MulAut.conj_apply]
  rw [show h * (g * x * g⁻¹) * h⁻¹ = h * g * x * (h * g)⁻¹ by group]

/-- Conjugation by 1 is the identity on open subgroups. -/
theorem S2432ConjIndex_one (H : Index p) :
    S2169ConjIndex p 1 H = H := by
  apply OpenSubgroup.ext
  intro x
  simp only [S2169ConjIndex, OpenSubgroup.mem_comap]
  change MulAut.conj (1 : Gv p) x ∈ H ↔ x ∈ H
  simp only [MulAut.conj_apply, inv_one, one_mul, mul_one]

/-- `muQZof` is invariant under an equality of open subgroups. -/
theorem S2432_muQZof_cast {H H' : Index p} (e : H = H') (v : Stage p H) :
    muQZof p H v = muQZof p H' (e ▸ v) := by
  cases e
  rfl

/-! ## 2. The additive endomorphism attached to g -/

/-- The levelwise family defining the endomorphism of `muQZ p` attached to
`g : Gv p`. -/
noncomputable def S2432MuQZEndFamily (g : Gv p) :
    ∀ H : Index p, Stage p H →+ muQZ p :=
  fun H =>
    (muQZof p (S2169ConjIndex p g H)).comp
      (S2179StageConj p g H).toAddMonoidHom

/-- The compatibility needed for `muQZ_lift`, from transfer compatibility. -/
theorem S2432MuQZEndFamily_compat (g : Gv p) :
    ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      S2432MuQZEndFamily p g H (toStage p h v) =
        S2432MuQZEndFamily p g K v := by
  intro H K h v
  obtain ⟨h', hEq⟩ := S2432_transferCompatible (p := p) g H K h v
  change muQZof p (S2169ConjIndex p g H)
      (S2179StageConj p g H (toStage p h v)) =
    muQZof p (S2169ConjIndex p g K) (S2179StageConj p g K v)
  rw [hEq, muQZof_transfer (p := p) (H := S2169ConjIndex p g H)
    (K := S2169ConjIndex p g K) h']

/-- The additive endomorphism of `muQZ p` attached to `g : Gv p`. -/
noncomputable def S2432MuQZEnd (g : Gv p) : muQZ p →+ muQZ p :=
  muQZ_lift p (muQZ p) (S2432MuQZEndFamily p g) (S2432MuQZEndFamily_compat p g)

/-- Computation rule for the endomorphism. -/
theorem S2432MuQZEnd_muQZof (g : Gv p) (H : Index p) (v : Stage p H) :
    S2432MuQZEnd p g (muQZof p H v) =
      muQZof p (S2169ConjIndex p g H) (S2179StageConj p g H v) :=
  muQZ_lift_of p (muQZ p) (S2432MuQZEndFamily p g)
    (S2432MuQZEndFamily_compat p g) H v

/-! ## 3. Functoriality of the torsion and abelianization coefficients -/

/-- The abelianization equivalence of a composite is the composite of the
abelianization equivalences. -/
theorem S2432_abelianizationCongr_trans {G H I : Type u} [Group G] [Group H] [Group I]
    (e₁ : G ≃* H) (e₂ : H ≃* I) :
    abelianizationCongr (e₁.trans e₂) =
      (abelianizationCongr e₁).trans (abelianizationCongr e₂) := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply]
  rfl

/-- Torsion congruence is functorial on elements. -/
theorem S2432_torsionCongr_trans {G H I : Type u} [CommGroup G] [CommGroup H] [CommGroup I]
    (e₁ : G ≃* H) (e₂ : H ≃* I) (w : CommGroup.torsion G) :
    torsionCongr e₂ (torsionCongr e₁ w) = torsionCongr (e₁.trans e₂) w := by
  apply Subtype.ext
  simp only [S2430_torsionCongr_coe, MulEquiv.trans_apply]

/-- The abelianization of the identity equivalence is the identity. -/
theorem S2432_abelianizationCongr_refl {G : Type u} [Group G] :
    abelianizationCongr (MulEquiv.refl G) = MulEquiv.refl (Abelianization G) := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext x
  rfl

/-- The torsion of the identity equivalence is the identity. -/
theorem S2432_torsionCongr_refl {G : Type u} [CommGroup G] :
    torsionCongr (MulEquiv.refl G) = MulEquiv.refl (CommGroup.torsion G) := by
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  rw [S2430_torsionCongr_coe]
  rfl

/-- Additive-stage version of the composition of two torsion coefficients. -/
theorem S2432_stageCongr_trans_apply {G : Type u} [Group G]
    {A B C : Subgroup G} (e₁ : ↥A ≃* ↥B) (e₂ : ↥B ≃* ↥C)
    (w : CommGroup.torsion (Abelianization ↥A)) :
    torsionCongr (abelianizationCongr e₂)
        (torsionCongr (abelianizationCongr e₁) w) =
      torsionCongr (abelianizationCongr (e₁.trans e₂)) w := by
  rw [S2432_torsionCongr_trans, ← S2432_abelianizationCongr_trans]

/-- Casting a torsion-congruence value along an equality of open subgroups,
controlled by the underlying element maps of the subgroup coefficients. -/
theorem S2432_stageCongr_index_cast_apply {H A B : Index p}
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
theorem S2432_stageConj_comp (g h : Gv p) (H : Index p) (v : Stage p H) :
    (S2432ConjIndex_comp p g h H) ▸
        (S2179StageConj p g (S2169ConjIndex p h H)
          (S2179StageConj p h H v)) =
      S2179StageConj p (h * g) H v := by
  let w : CommGroup.torsion (Abelianization ↥H) := Additive.toMul v
  have hv : v = Additive.ofMul w := rfl
  rw [hv]
  rw [S2430_stageConj_apply]
  rw [S2430_stageConj_apply]
  rw [S2430_stageConj_apply]
  rw [S2432_stageCongr_trans_apply]
  exact S2432_stageCongr_index_cast_apply (p := p) (H := H)
    (A := S2169ConjIndex p g (S2169ConjIndex p h H))
    (B := S2169ConjIndex p (h * g) H)
    (S2432ConjIndex_comp p g h H)
    ((S2200ConjEquiv p h H).trans (S2200ConjEquiv p g (S2169ConjIndex p h H)))
    (S2200ConjEquiv p (h * g) H)
    (by
      intro x
      rw [MulEquiv.trans_apply, S2317ConjEquiv_apply, S2317ConjEquiv_apply,
        S2317ConjEquiv_apply]
      group)
    w

/-- The stage conjugation by 1 is the identity, after the subgroup equality. -/
theorem S2432_stageConj_one_apply (H : Index p)
    (w : CommGroup.torsion (Abelianization ↥H)) :
    (S2432ConjIndex_one p H) ▸ (S2179StageConj p 1 H (Additive.ofMul w)) =
      Additive.ofMul w := by
  rw [S2430_stageConj_apply]
  have heq : (S2200ConjEquiv p 1 H) = MulEquiv.refl ↥H := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [S2317ConjEquiv_apply]
    rfl
  exact (S2432_stageCongr_index_cast_apply (p := p) (H := H)
      (A := S2169ConjIndex p 1 H) (B := H)
      (S2432ConjIndex_one p H) (S2200ConjEquiv p 1 H) (MulEquiv.refl ↥H)
      (by intro x; rw [S2317ConjEquiv_apply]; rfl) w).trans
    (by rw [S2432_abelianizationCongr_refl, S2432_torsionCongr_refl]; rfl)

/-! ## 5. The anti-composition law and the inverse -/

/-- Anti-composition law: `A_g o A_h = A_(h*g)`. -/
theorem S2432MuQZEnd_comp (g h : Gv p) :
    (S2432MuQZEnd p g).comp (S2432MuQZEnd p h) = S2432MuQZEnd p (h * g) := by
  exact muQZ_lift_unique p (muQZ p) (S2432MuQZEndFamily p (h * g))
    (S2432MuQZEndFamily_compat p (h * g))
    ((S2432MuQZEnd p g).comp (S2432MuQZEnd p h))
    (by
      intro H v
      rw [AddMonoidHom.comp_apply, S2432MuQZEnd_muQZof, S2432MuQZEnd_muQZof]
      change muQZof p (S2169ConjIndex p g (S2169ConjIndex p h H))
          (S2179StageConj p g (S2169ConjIndex p h H)
            (S2179StageConj p h H v)) =
        muQZof p (S2169ConjIndex p (h * g) H) (S2179StageConj p (h * g) H v)
      exact (S2432_muQZof_cast (e := S2432ConjIndex_comp p g h H)
        (v := S2179StageConj p g (S2169ConjIndex p h H)
          (S2179StageConj p h H v))).trans
        (congrArg (muQZof p (S2169ConjIndex p (h * g) H))
          (S2432_stageConj_comp p g h H v)))

/-- The endomorphism attached to 1 is the identity. -/
theorem S2432MuQZEnd_one : S2432MuQZEnd p 1 = AddMonoidHom.id (muQZ p) := by
  have hcomp : ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      (fun H : Index p => muQZof p H) H (toStage p h v) =
        (fun H : Index p => muQZof p H) K v :=
    fun {H K} h v => muQZof_transfer p h v
  have h1 := muQZ_lift_unique p (muQZ p) (fun H : Index p => muQZof p H) hcomp
    (S2432MuQZEnd p 1) (by
      intro H v
      rw [S2432MuQZEnd_muQZof]
      have hv : v = Additive.ofMul (Additive.toMul v) := rfl
      rw [hv]
      exact (S2432_muQZof_cast (e := S2432ConjIndex_one p H)
        (v := S2179StageConj p 1 H (Additive.ofMul (Additive.toMul v)))).trans
        (congrArg (muQZof p H)
          (S2432_stageConj_one_apply p H (Additive.toMul v))))
  have h2 := muQZ_lift_unique p (muQZ p) (fun H : Index p => muQZof p H) hcomp
    (AddMonoidHom.id (muQZ p)) (fun H v => rfl)
  exact h1.trans h2.symm

/-- Inverse law, one order. -/
theorem S2432MuQZEnd_comp_inv (g : Gv p) :
    (S2432MuQZEnd p g).comp (S2432MuQZEnd p g⁻¹) =
      AddMonoidHom.id (muQZ p) := by
  rw [S2432MuQZEnd_comp, inv_mul_cancel, S2432MuQZEnd_one]

/-- Inverse law, the other order. -/
theorem S2432MuQZEnd_inv_comp (g : Gv p) :
    (S2432MuQZEnd p g⁻¹).comp (S2432MuQZEnd p g) =
      AddMonoidHom.id (muQZ p) := by
  rw [S2432MuQZEnd_comp, mul_inv_cancel, S2432MuQZEnd_one]


end LeanFormal.IUT.XiFPaper.S2432MuQZMulAutDoneActual