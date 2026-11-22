/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import tmp.sheaf.lana_latest.Iut.Anabelian.Model
import tmp.sheaf.lana_latest.Iut.Anabelian.Genuine.Orbifold
import tmp.sheaf.lana_latest.Iut.Anabelian.Genuine.Theory
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Andre.FieldChangeDirect
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Andre.OrbStageFunctor
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Andre.TateNodeChart
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Andre.TateProjection
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Andre.TateRestrictIUT
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Andre.TateWildFin
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Andre.TempSlim
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Andre.TransferCompare
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Andre.WDualGraphMap
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.FibreFunctor.Realization
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Orbicurve.Orbifold
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemiAnbd.Anabelioid
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemiAnbd.MidpointAdj
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.AnnulusGerm
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.AnnulusRecognition
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.ChartModuleNakayama
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.EtaleBaseChange
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.EtaleLiftUnique
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.KummerNodeData
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueReduced
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.NormalisedModel
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.PointReduction
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.SplitAfterExtension
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.TateChartFinite
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.TateFlatAlgebraization
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.TwoChartStructureMap
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.ZariskiAlgebraDescent
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.SemistableReduction.ZariskiHarmonic
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Setup.Schmidt
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Tempered.EtaleOrbCover
import tmp.sheaf.lana.tempered_fundamental_groups.TemperedFundamentalGroups.Tempered.Kummer
/-!
# Tempered fundamental groups of the model orbicurves (taxis #7)

(The imports are all of `TemperedFundamentalGroups` except the six modules over
`SemistableReduction.LinearProjectionKer`, whose instance
`Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` is also declared by `oka`'s
`AlgebraicGeometry.Modules.Support`, which `curves-jacobian` imports.)

This module builds the tempered fundamental groups of the model orbicurves over the
genuine étale fundamental groups `Orbicurve.genuinePi1 X = Genuine.pi1C E ℓ M ±` of the model
orbicurves (`Iut.Anabelian.Genuine.Theory`: `Aut(Ω / F_X) ⧸ ⟨⟨inertia over X_M⟩⟩` in
characteristic `0`, the trivial group otherwise), from the
construction of lana-agents/tempered-fundamental-groups, with **no comparison parameter**: the
tempered and the étale fundamental group are computed from the same presentation.

* In characteristic `0`, a model orbicurve `X = (E, ℓ, M, ±)` over `k` is presented as the
  affine orbifold `[Spec R / A]` of `Iut.Anabelian.Genuine.orbifold`: `R` is the integral closure
  of `k[x]` in the function field `L_X = Ω^{Aut(Ω / L_X)}` and `A = Aut(Ω / F_X) ⧸ Aut(Ω / L_X)`,
  at the geometric point `R ⊆ Ω` (`Ω` an algebraic closure of `k(E)`). Its étale fundamental
  group `Pi1.Orbifold.etalePi1 R A Ω` is identified with `Genuine.pi1Of E ℓ M ±` by
  `Genuine.etaleEquiv` (SGA 1 V.8.2 with a finite group action, from the `pi1` project), and
  `Genuine.pi1Of E ℓ M ± = Genuine.pi1C E ℓ M ±` by `Genuine.pi1EquivC`.
* `Orbicurve.temperedPi1 X` is `TemperedFundamentalGroups.AffineOrbifold.canonicalTemperedPi1` of
  this
  presentation: the tempered fundamental group over the canonical valuation of `k` (the
  henselian discrete valuation ring of `k` if there is one — by F. K. Schmidt's theorem it is
  unique, so it is `O_v` for the completions `K_v` — and the trivial valuation otherwise),
  extended to `Ω` by the chosen extension of valuation rings (see that repository's
  `Blueprint.md` for the identification with André's definition and what is cited there).
* `Orbicurve.tempToEtale X` is the tempered-to-étale comparison `AffineOrbifold.temperedToEtale` of
  the
  presentation followed by `Genuine.etaleEquiv`.
* **Outside characteristic `0`** (where the comparison `Genuine.etaleEquiv` is not available)
  the tempered group is that of the geometric presentation `Orbicurve.affineOrbifold`
  (`[(E ∖ (E[ℓ] + M)) / A]` at the generic point) and `tempToEtale X` is the trivial
  homomorphism. This is a junk value: IUT only evaluates the theory over fields of
  characteristic `0` (the genuine cores are also only defined in characteristic `0`).

`Orbicurve.temperedPi1 X` is the resulting tempered fundamental group and
`Orbicurve.tempToEtale X : X.temperedPi1 →* X.genuinePi1` the continuous comparison. The
genuine covers and `k`-cores are in `Iut.Anabelian.GenuineEtale`.

**Honesty note.** The tempered group is the integral-model construction of
lana-agents/tempered-fundamental-groups. It is identified with André's tempered fundamental
group of the same presentation in `Iut.Anabelian.TemperedAndre` (`Orbicurve.temperedEquivAndre`,
by `TemperedFundamentalGroups.andreEquiv'`), and unconditionally at the places of initial
Θ-data in `Iut.Cor312.ThetaData.AndreLocal` (`LocalThetaData.pivBadEquivAndre`).
-/

namespace Iut.Anabelian

universe u

open TemperedFundamentalGroups

-- the decidability instances of `Iut.Anabelian.Model` (points of `E` need `DecidableEq k`)
attribute [local instance low] Classical.propDecidable

noncomputable section

/-- **The geometric affine presentation** of a model orbicurve: `[Spec R / A]` with
`Spec R = E ∖ S`, `S = E(k)[ℓ] + M`, `A = {P ↦ εP + m}`, at the generic geometric point. -/
def Orbicurve.affineOrbifold {k : Type u} [Field k] (X : Orbicurve k) : AffineOrbifold k :=
  TemperedFundamentalGroups.Orbicurve.orbicurveOrbifold X.E X.level X.M X.pm

/-- **The étale fundamental group** of a model orbicurve used by the genuine étale theory
(`Genuine.pi1C`): the genuine étale fundamental group `Genuine.pi1Of` in characteristic `0`
(`Genuine.pi1EquivC`), the trivial group (a junk value) in positive characteristic. -/
abbrev Orbicurve.genuinePi1 {k : Type u} [Field k] (X : Orbicurve k) : ProfiniteGrp.{u} :=
  Genuine.pi1C X.E X.level X.M X.pm

/-- **The presentation used for the tempered fundamental group**, with the continuous comparison
of its étale fundamental group with the genuine one: in characteristic `0`, the Galois
presentation `Genuine.orbifold` with the isomorphism `Genuine.etaleEquiv`; otherwise (a junk
value, never evaluated by IUT) the geometric presentation with the trivial homomorphism. -/
def Orbicurve.temperedPresentation {k : Type u} [Field k] (X : Orbicurve k) :
    Σ Y : AffineOrbifold k, {φ : Y.etalePi1 →* X.genuinePi1 // Continuous φ} :=
  if h : CharZero k then
    haveI := h
    ⟨Genuine.orbifold X.E X.level X.M X.pm,
      ((Genuine.etaleEquiv X.E X.level X.M X.pm).trans
        (Genuine.pi1EquivC X.E X.level X.M X.pm)).toMulEquiv.toMonoidHom,
      ((Genuine.etaleEquiv X.E X.level X.M X.pm).trans
        (Genuine.pi1EquivC X.E X.level X.M X.pm)).continuous⟩
  else ⟨X.affineOrbifold, 1, continuous_const⟩

lemma Orbicurve.temperedPresentation_of_charZero {k : Type u} [Field k] [CharZero k]
    (X : Orbicurve k) :
    X.temperedPresentation = ⟨Genuine.orbifold X.E X.level X.M X.pm,
      ((Genuine.etaleEquiv X.E X.level X.M X.pm).trans
        (Genuine.pi1EquivC X.E X.level X.M X.pm)).toMulEquiv.toMonoidHom,
      ((Genuine.etaleEquiv X.E X.level X.M X.pm).trans
        (Genuine.pi1EquivC X.E X.level X.M X.pm)).continuous⟩ := by
  rw [Orbicurve.temperedPresentation, dif_pos (inferInstance : CharZero k)]

/-- **The tempered fundamental group** of a model orbicurve: the tempered fundamental group
`TemperedFundamentalGroups.AffineOrbifold.canonicalTemperedPi1` of the presentation
`Orbicurve.temperedPresentation` (the construction through integral models of
lana-agents/tempered-fundamental-groups, over the canonical valuation of the base field). Its
identification with André's tempered fundamental group is the business of that repository. -/
abbrev Orbicurve.temperedPi1 {k : Type u} [Field k] (X : Orbicurve k) : Type u :=
  X.temperedPresentation.1.canonicalTemperedPi1

/-- **The comparison homomorphism** from the tempered to the genuine étale fundamental group:
the tempered-to-étale comparison of the presentation, followed by the identification of its
étale fundamental group with `Orbicurve.genuinePi1` (the trivial homomorphism outside
characteristic `0`, a junk value). -/
def Orbicurve.tempToEtale {k : Type u} [Field k] (X : Orbicurve k) :
    X.temperedPi1 →* X.genuinePi1 :=
  X.temperedPresentation.2.1.comp (X.temperedPresentation.1.temperedToEtale _)

/-- The comparison homomorphism is continuous. -/
lemma Orbicurve.continuous_tempToEtale {k : Type u} [Field k] (X : Orbicurve k) :
    Continuous X.tempToEtale :=
  X.temperedPresentation.2.2.comp (X.temperedPresentation.1.continuous_temperedToEtale _)

end

end Iut.Anabelian
