import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

/-!
# Strip-side units actions from supplied `Pi`-factorizations

Conditional supply for the actions sub-obligation of `G1-SRC-a`
(`logs/coordination/outsider-survey-transport-20261016.md`, sections 19.2-19.4;
routing adjudication in `logs/coordination/source-ftimesmu-strip-20261016.md`,
`t7.9`).

Source anchor: IUT II, Definition 4.9, (i) attaches to each strip the action
of the arithmetic group on the unit groups of its `v`-components through the
prime-strip data; IUT III, Theorem 3.11, (ii), (iii)(c)(d) and Remark 3.10.2
write the Kummer and evaluation arrows with exactly such actions.

Supplied here (conditional): for an abstract group `G` and a *given*
factorization `g : ∀ v, G →* toDPrimeStrip.Pi v`, the induced units
action `(F.unitsAction v).comp (g v)` on `(F.Mon v)ˣ`, its quotient companion
on the times-mu layers, naturality under post-composition of the
factorization, and equivariance under `FPrimeStripEquiv` through the existing
interface `FPrimeStripEquiv.unitsAction_compat`.

NOT claimed: the factorization `g` itself is not constructed.  Its source is
the kappa-orbit data of IUT II, Definition 4.9, (i), which stays with the
source-input line; this file is the strip-side conditional form only.

Consumer: the `sourceAction`/`targetAction` slots of `SourceTimesMuKummerLayer`
(`SourceKummerEvaluationArrows.lean:130-139`) and of
`SourceEvaluationUnitPortion` (`SourceKummerEvaluationArrows.lean:249-259`),
reached through `sheSupply` in the SHE transport chain.
-/

namespace LeanFormal.IUT

universe uG uH uv umon upi

variable {V : Type uv}

namespace FPrimeStrip

variable (F : FPrimeStrip V)

/-- The units action induced by a supplied factorization
`g : ∀ v, G →* F.toDPrimeStrip.Pi v`, namely the composite of
`F.unitsAction v` with `g v`.  Conditional form of the actions datum of
IUT II, Definition 4.9, (i); the factorization itself is supplied data, not
constructed here. -/
def unitsActionOfFactorization {G : Type uG} [Group G]
    (g : ∀ v, G →* F.toDPrimeStrip.Pi v) (v : V) :
    G →* MulAut (F.Mon v)ˣ :=
  (F.unitsAction v).comp (g v)

variable {F}

@[simp] theorem unitsActionOfFactorization_apply {G : Type uG} [Group G]
    (g : ∀ v, G →* F.toDPrimeStrip.Pi v) (v : V) (γ : G)
    (u : (F.Mon v)ˣ) :
    (F.unitsActionOfFactorization g v γ) u =
      F.unitsAction v (g v γ) u := rfl

@[simp] theorem unitsActionOfFactorization_val {G : Type uG} [Group G]
    (g : ∀ v, G →* F.toDPrimeStrip.Pi v) (v : V) (γ : G)
    (u : (F.Mon v)ˣ) :
    (F.unitsActionOfFactorization g v γ u : F.Mon v) =
      F.action v (g v γ) (u : F.Mon v) :=
  FPrimeStrip.unitsAction_val F v (g v γ) u

/-- Naturality of the construction in the factorization: re-parameterizing
`g` along a group homomorphism `h : H →* G` gives the composite action. -/
theorem unitsActionOfFactorization_comp {G : Type uG} {H : Type uH}
    [Group G] [Group H] (g : ∀ v, G →* F.toDPrimeStrip.Pi v)
    (h : H →* G) (v : V) :
    F.unitsActionOfFactorization (fun v => (g v).comp h) v =
      (F.unitsActionOfFactorization g v).comp h := rfl

/-- The quotient companion: the induced action on the times-mu layers. -/
def timesMuActionOfFactorization {G : Type uG} [Group G]
    (g : ∀ v, G →* F.toDPrimeStrip.Pi v) (v : V) :
    G →* MulAut (F.timesMuQuotient v) :=
  (F.timesMuAction v).comp (g v)

@[simp] theorem timesMuActionOfFactorization_apply {G : Type uG} [Group G]
    (g : ∀ v, G →* F.toDPrimeStrip.Pi v) (v : V) (γ : G)
    (x : F.timesMuQuotient v) :
    F.timesMuActionOfFactorization g v γ x =
      F.timesMuAction v (g v γ) x := rfl

/-- Interface law: the induced times-mu action is the descended action
(`TimesMuQuotient.action`) of the induced units action. -/
theorem timesMuActionOfFactorization_eq_action {G : Type uG} [Group G]
    (g : ∀ v, G →* F.toDPrimeStrip.Pi v) (v : V) :
    F.timesMuActionOfFactorization g v =
      TimesMuQuotient.action (F.unitsActionOfFactorization g v) := rfl

@[simp] theorem timesMuActionOfFactorization_quotientMap {G : Type uG} [Group G]
    (g : ∀ v, G →* F.toDPrimeStrip.Pi v) (v : V) (γ : G)
    (u : (F.Mon v)ˣ) :
    F.timesMuActionOfFactorization g v γ (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (F.unitsActionOfFactorization g v γ u) :=
  FPrimeStrip.timesMuAction_quotientMap F v (g v γ) u

end FPrimeStrip

namespace FPrimeStripEquiv

variable {F F' : FPrimeStrip.{umon, uv, upi} V}

/-- Equivariance of the induced units actions under a strip equivalence: if
`φ.isoPi v` carries the factorization `g` into `g'`, then `φ.isoMon v`
carries the action induced by `g` into the action induced by `g'`.  This is
the compatibility of the construction with the existing equivariance
interface `FPrimeStripEquiv.unitsAction_compat`
(`SourceFTimesMuPrimeStripPolyIsomorphism.lean:83`). -/
theorem unitsActionOfFactorization_compat {G : Type uG} [Group G]
    (φ : FPrimeStripEquiv F F')
    (g : ∀ v, G →* F.toDPrimeStrip.Pi v)
    (g' : ∀ v, G →* F'.toDPrimeStrip.Pi v)
    (hg : ∀ v γ, φ.isoPi v (g v γ) = g' v γ)
    (v : V) (γ : G) (u : (F.Mon v)ˣ) :
    Units.mapEquiv (φ.isoMon v) (F.unitsActionOfFactorization g v γ u) =
      F'.unitsActionOfFactorization g' v γ
        (Units.mapEquiv (φ.isoMon v) u) := by
  change Units.mapEquiv (φ.isoMon v)
      (FPrimeStrip.unitsAction F v (g v γ) u) =
    FPrimeStrip.unitsAction F' v (g' v γ)
      (Units.mapEquiv (φ.isoMon v) u)
  rw [← hg v γ]
  exact FPrimeStripEquiv.unitsAction_compat φ v (g v γ) u

end FPrimeStripEquiv

namespace Audit

/-- Conditional supply of the `G1-SRC-a` actions sub-obligation (strip side):
units actions induced by supplied `Pi`-factorizations, with their quotient,
naturality and equivariance laws.  The kappa-orbit construction of the
factorization remains with the source-input line. -/
def stripUnitsActionFactorization : Obligation :=
  { id := "IUT-II.prime-strips-units-action-factorization"
    source :=
      "IUT II, Definition 4.9, (i); IUT III, Theorem 3.11, (ii), (iii)(c)(d); " ++
        "Remark 3.10.2"
    status := VerificationStatus.interface
    note :=
      "CONDITIONAL strip-side supply for the G1-SRC-a actions sub-obligation. " ++
        "Given a factorization g : ∀ v, G →* toDPrimeStrip.Pi v, " ++
        "`FPrimeStrip.unitsActionOfFactorization` is `(F.unitsAction v).comp (g v)` " ++
        "with apply/val laws, the times-mu companion " ++
        "`timesMuActionOfFactorization` with its descent law " ++
        "(`timesMuActionOfFactorization_eq_action`) and the quotientMap law, " ++
        "naturality in the factorization (`unitsActionOfFactorization_comp`) and " ++
        "equivariance under `FPrimeStripEquiv` through the existing interface " ++
        "`unitsAction_compat` (`unitsActionOfFactorization_compat`). " ++
        "NOT CLAIMED: the factorization g itself; its kappa-orbit source " ++
        "(IUT II, Def 4.9, (i)) stays with the source-input line. Consumers: the " ++
        "sourceAction/targetAction slots of `SourceTimesMuKummerLayer` and " ++
        "`SourceEvaluationUnitPortion` (Theorem311 SourceKummerEvaluationArrows), " ++
        "reached via sheSupply."
    dependsOn :=
      [ "IUT-I-II.prime-strip-core",
        "IUT-II.prime-strips-frobenioid-category-skeleton" ] }

end Audit

end LeanFormal.IUT
