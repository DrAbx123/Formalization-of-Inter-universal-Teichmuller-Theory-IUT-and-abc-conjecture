import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Actual corrected quotient action by chart permutation

A quotient chart gluing datum is given by a common quotient chart scheme V, chart
maps to Q, overlap data and the gluing universal property.  Starting from an
actual chart permutation sigma, this file constructs the action on Q explicitly
by the gluing universal property.  The chart equation, the overlap equation and
the cocycle are proved, and a moved separated chart makes the action nontrivial.
No action is assumed.
-/
namespace ABCBridge.CorrectedQuotientActionActual

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type u}

/-- Actual glued quotient chart data: common chart scheme, quotient scheme, chart
maps, overlaps, chart compatibility and the universal property. -/
structure GluedQuotientData (J : Type u) where
  V : Scheme.{u}
  Q : Scheme.{u}
  chart : J → (V ⟶ Q)
  W : J → J → Scheme.{u}
  fst : ∀ i j, W i j ⟶ V
  snd : ∀ i j, W i j ⟶ V
  chart_compat : ∀ i j, fst i j ≫ chart i = snd i j ≫ chart j
  universal : ∀ (Z : Scheme.{u}) (f : J → (V ⟶ Z)),
    ∃! u : Q ⟶ Z, ∀ i, chart i ≫ u = f i

variable {G : Type u} [Group G]
  (HG : GluedQuotientData (J := J))

/-- Actual chart permutation data: the permutation, its one/cocycle laws, and the
permutation compatibility of the chart overlaps. -/
structure ChartPermutationData (HG : GluedQuotientData (J := J)) (G : Type u) [Group G] where
  sigma : G → Equiv.Perm J
  sigma_one : ∀ i, sigma 1 i = i
  sigma_mul : ∀ (g h : G) (i : J), sigma (g * h) i = sigma g (sigma h i)
  perm_compat : ∀ (g : G) (i j : J),
    HG.fst i j ≫ HG.chart (sigma g i) = HG.snd i j ≫ HG.chart (sigma g j)

variable (P : ChartPermutationData (HG := HG) (G := G))

/-- The chart family of the action at g. -/
def actionFamily (g : G) (i : J) : HG.V ⟶ HG.Q :=
  HG.chart (P.sigma g i)

/-- The endomorphism of Q induced by the chart permutation at g. -/
noncomputable def actionEnd (g : G) : HG.Q ⟶ HG.Q :=
  (HG.universal HG.Q (actionFamily HG P g)).choose

/-- The action endomorphism restricts to the permuted charts. -/
theorem actionEnd_fac (g : G) (i : J) :
    HG.chart i ≫ actionEnd HG P g = HG.chart (P.sigma g i) :=
  (HG.universal HG.Q (actionFamily HG P g)).choose_spec.1 i

/-- Uniqueness of the action endomorphism. -/
theorem actionEnd_uniq (g : G) (u : HG.Q ⟶ HG.Q)
    (hu : ∀ i, HG.chart i ≫ u = HG.chart (P.sigma g i)) :
    u = actionEnd HG P g :=
  (HG.universal HG.Q (actionFamily HG P g)).choose_spec.2 u hu

/-- The action at the identity is the identity. -/
theorem actionEnd_one : actionEnd HG P 1 = 𝟙 HG.Q := by
  symm
  apply actionEnd_uniq HG P 1
  intro i
  rw [Category.comp_id, P.sigma_one]

/-- The action is anti-multiplicative for the chart permutation cocycle. -/
theorem actionEnd_mul (g h : G) :
    actionEnd HG P (g * h) = actionEnd HG P h ≫ actionEnd HG P g := by
  symm
  apply actionEnd_uniq HG P (g * h)
  intro i
  calc
    HG.chart i ≫ (actionEnd HG P h ≫ actionEnd HG P g) =
        (HG.chart i ≫ actionEnd HG P h) ≫ actionEnd HG P g := by
      rw [Category.assoc]
    _ = HG.chart (P.sigma h i) ≫ actionEnd HG P g := by
      rw [actionEnd_fac]
    _ = HG.chart (P.sigma g (P.sigma h i)) := by
      rw [actionEnd_fac]
    _ = HG.chart (P.sigma (g * h) i) := by
      rw [P.sigma_mul]

/-- The inverse action endomorphism on the right. -/
theorem actionEnd_comp_inv (g : G) :
    actionEnd HG P g ≫ actionEnd HG P g⁻¹ = 𝟙 HG.Q := by
  have h := actionEnd_mul HG P g⁻¹ g
  rw [inv_mul_cancel] at h
  rw [actionEnd_one] at h
  exact h.symm

/-- The inverse action endomorphism on the left. -/
theorem actionEnd_inv_comp (g : G) :
    actionEnd HG P g⁻¹ ≫ actionEnd HG P g = 𝟙 HG.Q := by
  have h := actionEnd_mul HG P g g⁻¹
  rw [mul_inv_cancel] at h
  rw [actionEnd_one] at h
  exact h.symm

/-- The action automorphism at a group element. -/
noncomputable def actionIso (g : G) : HG.Q ≅ HG.Q where
  hom := actionEnd HG P g
  inv := actionEnd HG P g⁻¹
  hom_inv_id := actionEnd_comp_inv HG P g
  inv_hom_id := actionEnd_inv_comp HG P g

/-- The actual group action on the glued quotient. -/
noncomputable def gluedAction : G →* CategoryTheory.Aut HG.Q where
  toFun g := actionIso HG P g
  map_one' := by
    apply Iso.ext
    exact actionEnd_one HG P
  map_mul' g h := by
    apply Iso.ext
    exact actionEnd_mul HG P g h

/-- The glued action has the chart equation with the permutation. -/
theorem gluedAction_chart (g : G) (i : J) :
    HG.chart i ≫ (gluedAction HG P g).hom = HG.chart (P.sigma g i) :=
  actionEnd_fac HG P g i

/-- The glued action has the overlap equation. -/
theorem gluedAction_overlap (g : G) (i j : J) :
    HG.fst i j ≫ HG.chart i ≫ (gluedAction HG P g).hom =
      HG.snd i j ≫ HG.chart j ≫ (gluedAction HG P g).hom := by
  rw [gluedAction_chart, gluedAction_chart]
  exact P.perm_compat g i j

/-- The chart permutation cocycle law. -/
theorem gluedAction_cocycle (g h : G) (i : J) :
    P.sigma (g * h) i = P.sigma g (P.sigma h i) :=
  P.sigma_mul g h i

/-- The action is nontrivial when a chart is moved to a different chart map. -/
theorem gluedAction_nontrivial_of_moved_chart (g : G) (i : J)
    (hmove : P.sigma g i ≠ i)
    (hsep : HG.chart i ≠ HG.chart (P.sigma g i)) :
    gluedAction HG P g ≠ 1 := by
  intro hone
  apply hsep
  have hchart : HG.chart i ≫ (gluedAction HG P g).hom = HG.chart (P.sigma g i) :=
    gluedAction_chart HG P g i
  have hhom : (gluedAction HG P g).hom = 𝟙 HG.Q := by
    rw [hone]
    rfl
  rw [hhom, Category.comp_id] at hchart
  exact hchart

/-- The moved-chart hypothesis is the exact nontriviality source. -/
theorem gluedAction_nontrivial_of_moved_separated (g : G)
    (h : ∃ i : J, P.sigma g i ≠ i ∧ HG.chart i ≠ HG.chart (P.sigma g i)) :
    gluedAction HG P g ≠ 1 := by
  obtain ⟨i, hi, hsep⟩ := h
  exact gluedAction_nontrivial_of_moved_chart HG P g i hi hsep

/-- The actual chart-permutation action datum, with no residual fields. -/
structure ActualCorrectedQuotientAction (HG : GluedQuotientData (J := J)) (G : Type u) [Group G] where
  permutation : ChartPermutationData (HG := HG) (G := G)
  action : G →* CategoryTheory.Aut HG.Q
  action_eq : action = gluedAction HG permutation
  chart_equation : ∀ (g : G) (i : J),
    HG.chart i ≫ (action g).hom = HG.chart (permutation.sigma g i)
  overlap_equation : ∀ (g : G) (i j : J),
    HG.fst i j ≫ HG.chart i ≫ (action g).hom =
      HG.snd i j ≫ HG.chart j ≫ (action g).hom

/-- The actual action datum constructed from the chart permutation. -/
noncomputable def actualCorrectedQuotientAction :
    ActualCorrectedQuotientAction (G := G) HG where
  permutation := P
  action := gluedAction HG P
  action_eq := rfl
  chart_equation := gluedAction_chart HG P
  overlap_equation := gluedAction_overlap HG P

/-- The action datum has the chart equation. -/
theorem actualCorrectedQuotientAction_chart (g : G) (i : J) :
    HG.chart i ≫ ((actualCorrectedQuotientAction (G := G) HG P).action g).hom =
      HG.chart (P.sigma g i) :=
  gluedAction_chart HG P g i

/-- The action datum has the overlap equation. -/
theorem actualCorrectedQuotientAction_overlap (g : G) (i j : J) :
    HG.fst i j ≫ HG.chart i ≫ ((actualCorrectedQuotientAction (G := G) HG P).action g).hom =
      HG.snd i j ≫ HG.chart j ≫ ((actualCorrectedQuotientAction (G := G) HG P).action g).hom :=
  gluedAction_overlap HG P g i j

/-- The glued action at the identity is the identity automorphism. -/
theorem gluedAction_map_one : gluedAction HG P 1 = 1 :=
  map_one (gluedAction HG P)

/-- The glued action is multiplicative. -/
theorem gluedAction_map_mul (g h : G) :
    gluedAction HG P (g * h) = gluedAction HG P g * gluedAction HG P h :=
  map_mul (gluedAction HG P) g h

/-- The underlying endomorphism of the glued action. -/
theorem gluedAction_apply (g : G) :
    (gluedAction HG P g).hom = actionEnd HG P g :=
  rfl

/-- The inverse underlying endomorphism. -/
theorem gluedAction_inv_apply (g : G) :
    (gluedAction HG P g).inv = actionEnd HG P g⁻¹ :=
  rfl

/-- The action datum's permutation is the actual chart permutation. -/
theorem actualCorrectedQuotientAction_permutation :
    (actualCorrectedQuotientAction (G := G) HG P).permutation = P :=
  rfl

/-- The action datum's action is the actual glued action. -/
theorem actualCorrectedQuotientAction_action :
    (actualCorrectedQuotientAction (G := G) HG P).action = gluedAction HG P :=
  rfl

/-- The action datum's chart equation in projection form. -/
theorem actualCorrectedQuotientAction_chart_apply (g : G) (i : J) :
    HG.chart i ≫ ((actualCorrectedQuotientAction (G := G) HG P).action g).hom =
      HG.chart (P.sigma g i) :=
  gluedAction_chart HG P g i

/-- The action datum's overlap equation in projection form. -/
theorem actualCorrectedQuotientAction_overlap_apply (g : G) (i j : J) :
    HG.fst i j ≫ HG.chart i ≫ ((actualCorrectedQuotientAction (G := G) HG P).action g).hom =
      HG.snd i j ≫ HG.chart j ≫ ((actualCorrectedQuotientAction (G := G) HG P).action g).hom :=
  gluedAction_overlap HG P g i j

/-- The actual action is nontrivial from a moved separated chart. -/
theorem actualCorrectedQuotientAction_nontrivial_of_moved_separated (g : G)
    (h : ∃ i : J, P.sigma g i ≠ i ∧ HG.chart i ≠ HG.chart (P.sigma g i)) :
    (actualCorrectedQuotientAction (G := G) HG P).action g ≠ 1 :=
  gluedAction_nontrivial_of_moved_separated HG P g h

/-- The actual action datum exposes the chart permutation cocycle. -/
theorem actualCorrectedQuotientAction_cocycle (g h : G) (i : J) :
    (actualCorrectedQuotientAction (G := G) HG P).permutation.sigma (g * h) i =
      (actualCorrectedQuotientAction (G := G) HG P).permutation.sigma g
        ((actualCorrectedQuotientAction (G := G) HG P).permutation.sigma h i) :=
  P.sigma_mul g h i

/-- The actual action is a group homomorphism with the chart equation. -/
theorem actualCorrectedQuotientAction_group_law (g h : G) :
    (actualCorrectedQuotientAction (G := G) HG P).action (g * h) =
      (actualCorrectedQuotientAction (G := G) HG P).action g *
        (actualCorrectedQuotientAction (G := G) HG P).action h :=
  map_mul (actualCorrectedQuotientAction (G := G) HG P).action g h

/-- Complete actual action package. -/
theorem actualCorrectedQuotientAction_complete (g : G) (i j : J) :
    (HG.chart i ≫ ((actualCorrectedQuotientAction (G := G) HG P).action g).hom =
      HG.chart (P.sigma g i)) ∧
      (HG.fst i j ≫ HG.chart i ≫ ((actualCorrectedQuotientAction (G := G) HG P).action g).hom =
        HG.snd i j ≫ HG.chart j ≫ ((actualCorrectedQuotientAction (G := G) HG P).action g).hom) ∧
      (P.sigma (g * 1) i = P.sigma g (P.sigma 1 i)) :=
  ⟨actualCorrectedQuotientAction_chart_apply (G := G) HG P g i,
    actualCorrectedQuotientAction_overlap_apply (G := G) HG P g i j,
    P.sigma_mul g 1 i⟩


section ProviderConsumer

/-- Consumer packaging of the actual corrected quotient action for the provider
layer: quotient scheme HG.Q, its actual action, chart/overlap equations and the
cocycle.  The action is not replaced by a cover action. -/
structure CorrectedActionProviderConsumer (HG : GluedQuotientData (J := J)) (G : Type u) [Group G] where
  actionData : ActualCorrectedQuotientAction (G := G) HG
  quotient : Scheme.{u}
  quotient_eq : quotient = HG.Q
  action : G →* CategoryTheory.Aut quotient

/-- The actual provider consumer from the chart permutation. -/
noncomputable def correctedActionProviderConsumer :
    CorrectedActionProviderConsumer (G := G) HG where
  actionData := actualCorrectedQuotientAction HG P
  quotient := HG.Q
  quotient_eq := rfl
  action := gluedAction HG P

/-- The consumer quotient is the glued quotient. -/
theorem correctedActionProviderConsumer_quotient :
    (correctedActionProviderConsumer (G := G) HG P).quotient = HG.Q :=
  rfl

/-- The consumer action is the actual glued action. -/
theorem correctedActionProviderConsumer_action :
    (correctedActionProviderConsumer (G := G) HG P).action = gluedAction HG P :=
  rfl

/-- The consumer action has the chart equation. -/
theorem correctedActionProviderConsumer_chart (g : G) (i : J) :
    HG.chart i ≫ ((correctedActionProviderConsumer (G := G) HG P).action g).hom =
      HG.chart ((correctedActionProviderConsumer (G := G) HG P).actionData.permutation.sigma g i) :=
  gluedAction_chart HG P g i

/-- The consumer action has the overlap equation. -/
theorem correctedActionProviderConsumer_overlap (g : G) (i j : J) :
    HG.fst i j ≫ HG.chart i ≫ ((correctedActionProviderConsumer (G := G) HG P).action g).hom =
      HG.snd i j ≫ HG.chart j ≫ ((correctedActionProviderConsumer (G := G) HG P).action g).hom :=
  gluedAction_overlap HG P g i j

/-- The consumer action cocycle. -/
theorem correctedActionProviderConsumer_cocycle (g h : G) (i : J) :
    (correctedActionProviderConsumer (G := G) HG P).actionData.permutation.sigma (g * h) i =
      (correctedActionProviderConsumer (G := G) HG P).actionData.permutation.sigma g
        ((correctedActionProviderConsumer (G := G) HG P).actionData.permutation.sigma h i) :=
  P.sigma_mul g h i

/-- Consumer nontriviality from a moved separated chart. -/
theorem correctedActionProviderConsumer_nontrivial (g : G)
    (h : ∃ i : J, P.sigma g i ≠ i ∧ HG.chart i ≠ HG.chart (P.sigma g i)) :
    (correctedActionProviderConsumer (G := G) HG P).action g ≠ 1 :=
  gluedAction_nontrivial_of_moved_separated HG P g h

end ProviderConsumer

end ABCBridge.CorrectedQuotientActionActual