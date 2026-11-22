import tmp.sheaf.xif.paper.S2422StageDescent3Actual
import tmp.sheaf.xif.paper.S2371HnatExplicitActual

/-!
# S2430: torsion descent for the S2179 stage conjugation

Layer: O (S2179 stage compatibility, i.e. `S2179TransferCompatible`).
Consumer: `S2422StageDescentRequired` / `S2179TransferCompatible`.

The target `S2179TransferCompatible` asks, for `g : Gv p`, `H K : Index p`,
`h : H <= K` and `v : Stage p K`, for a witness `h' : conj H <= conj K` with

  S2179StageConj g H (toStage h v) = toStage h' (S2179StageConj g K v).

The coefficient of `S2179StageConj` on the underlying abelianization is the
map induced by `S2200ConjEquiv` (both are obtained from the same
`Subgroup.equivMapOfInjective`; `S2179StageConj` transports it along the
subgroup equality `S2179MapConjEqComap`, while `S2200ConjEquiv` composes with
`MulEquiv.subgroupCongr` of that equality).  Hence the pointwise torsion
equation follows from `S2371_verlagerung_natural` (`S2300VerlagerungNaturalRequired`)
applied to the underlying abelianization element, restricted to
`CommGroup.torsion`.

## Status

All declarations below are proved: `S2430_transferCompatible` closes
`S2179TransferCompatible` (equivalently `S2422StageDescentRequired`), and the
axiom probes list only `propext`, `Classical.choice`, `Quot.sound`.  There is
no `sorry`, no auxiliary axiom and no fabricated object in this file; the
first missing item is none for this surface.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2430TorsionDescentSubagentActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2371HnatExplicitActual
open LeanFormal.IUT.XiFPaper.S2422StageDescent3Actual

universe u

/-- Transporting a `MulEquiv` of subgroups along an equality of the target
subgroups agrees with composing with `MulEquiv.subgroupCongr`. -/
theorem S2430_cast_equiv_eq_trans {G : Type u} [Group G]
    {X A B : Subgroup G} (h : A = B) (e : ↥X ≃* ↥A) :
    (h ▸ e : ↥X ≃* ↥B) = e.trans (MulEquiv.subgroupCongr h) := by
  cases h
  ext x
  rfl

/-- Coercion formula for the torsion equivalence induced by a multiplicative
equivalence. -/
theorem S2430_torsionCongr_coe {A B : Type u} [CommGroup A] [CommGroup B]
    (e : A ≃* B) (w : CommGroup.torsion A) :
    ((torsionCongr e w : CommGroup.torsion B) : B) = e (w : A) := by
  rfl

/-- Coercion formula for the restriction of a homomorphism to torsion. -/
theorem S2430_torsionMap_coe {A B : Type u} [CommGroup A] [CommGroup B]
    (f : A →* B) (w : CommGroup.torsion A) :
    ((torsionMap f w : CommGroup.torsion B) : B) = f (w : A) := by
  rfl

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The additive transfer map `toStage` on a torsion element written in
multiplicative notation. -/
theorem S2430_toStage_apply {H K : Index p} (h : H ≤ K)
    (w : CommGroup.torsion (Abelianization ↥K)) :
    toStage p h (Additive.ofMul w) =
      Additive.ofMul (torsionMap (verlagerungOpen p h) w) := by
  rfl

/-- The underlying abelianization coefficient of `S2179StageConj` is the one
of `S2200ConjEquiv`. -/
theorem S2430_stageConj_eq (g : Gv p) (H : Index p) :
    S2179StageConj p g H =
      (torsionCongr (abelianizationCongr (S2200ConjEquiv p g H))).toAdditive := by
  unfold S2179StageConj
  dsimp only
  rw [S2430_cast_equiv_eq_trans]
  rfl

/-- Pointwise form of `S2430_stageConj_eq` on a torsion element. -/
theorem S2430_stageConj_apply (g : Gv p) (H : Index p)
    (w : CommGroup.torsion (Abelianization ↥H)) :
    S2179StageConj p g H (Additive.ofMul w) =
      Additive.ofMul (torsionCongr (abelianizationCongr (S2200ConjEquiv p g H)) w) := by
  rw [S2430_stageConj_eq]
  rfl

/-- **Main result**: the S2179 stage conjugation is compatible with the
transfer maps, i.e. `S2179TransferCompatible` holds. -/
theorem S2430_transferCompatible : S2179TransferCompatible (p := p) := by
  intro g H K h v
  obtain ⟨h', hnat⟩ := S2371_verlagerung_natural (p := p) g H K h
  refine ⟨h', ?_⟩
  let w : CommGroup.torsion (Abelianization ↥K) := Additive.toMul v
  have hv : v = Additive.ofMul w := rfl
  rw [hv]
  rw [S2430_toStage_apply]
  rw [S2430_stageConj_apply]
  rw [S2430_stageConj_apply]
  rw [S2430_toStage_apply]
  apply Additive.ext
  apply Subtype.ext
  simp only [toMul_ofMul, S2430_torsionCongr_coe, S2430_torsionMap_coe]
  exact DFunLike.congr_fun hnat (w : Abelianization ↥K)

/-- The S2422 stage-descent surface, obtained from the fully proved S2179
transfer compatibility. -/
theorem S2430_stageDescentRequired : S2422StageDescentRequired (p := p) :=
  S2430_transferCompatible p

#check S2430_cast_equiv_eq_trans
#check S2430_torsionCongr_coe
#check S2430_torsionMap_coe
#check S2430_toStage_apply
#check S2430_stageConj_eq
#check S2430_stageConj_apply
#check S2430_transferCompatible
#check S2430_stageDescentRequired

#print axioms S2430_cast_equiv_eq_trans
#print axioms S2430_torsionCongr_coe
#print axioms S2430_torsionMap_coe
#print axioms S2430_toStage_apply
#print axioms S2430_stageConj_eq
#print axioms S2430_stageConj_apply
#print axioms S2430_transferCompatible
#print axioms S2430_stageDescentRequired

end LeanFormal.IUT.XiFPaper.S2430TorsionDescentSubagentActual

end