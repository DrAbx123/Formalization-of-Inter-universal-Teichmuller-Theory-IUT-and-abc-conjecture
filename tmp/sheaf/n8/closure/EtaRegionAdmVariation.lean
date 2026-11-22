import tmp.sheaf.n8.closure.EtaRegionAdmCorrect
import tmp.sheaf.n8.closure.EtaRssNontrivialActual
import tmp.sheaf.n8.closure.P6AdmRedesign

/-!
# Eta region Adm variation

Actual corrected RegionAdmCorrect regions with finite support and positive finite
mass, whose bad-place masses differ.  The varying-region Rss is the global
equal-mass-at-bad-place quotient; the two regions give distinct classes.

Regions:
- openGlobalRegion: actual open unit ball at badPlace X, integralReference
  elsewhere;
- closedGlobalRegion: actual closed unit ball at badPlace X,
  integralReference elsewhere.

No empty/univ or arbitrary region is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRegionAdmVariation

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6AdmRedesign
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.EtaRegionAdmCorrect
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)]

/-- Actual open-ball global region. -/
noncomputable def openGlobalRegion : GlobalRegion X := by
  classical
  exact fun v =>
    if v = badPlace X then Metric.ball (0 : localFieldAt X v) (1 : ℝ)
    else integralReference X v

/-- Actual closed-ball global region. -/
noncomputable def closedGlobalRegion : GlobalRegion X := by
  classical
  exact fun v =>
    if v = badPlace X then Metric.closedBall (0 : localFieldAt X v) (1 : ℝ)
    else integralReference X v

/-- Equal mass at the bad native place. -/
def SameBadMass (reference region : GlobalRegion X) : Prop :=
  mu (badPlace X) (reference (badPlace X)) =
    mu (badPlace X) (region (badPlace X))

def sameBadMassSetoid : Setoid (GlobalRegion X) where
  r := SameBadMass X mu
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro R; rfl
    · intro R S h; exact h.symm
    · intro R S T hRS hST; exact hRS.trans hST

/-- Varying-region Rss. -/
abbrev VaryingRegionRss : Type _ := Quotient (sameBadMassSetoid X mu)

/-- Exact variation statement. -/
def EtaRegionAdmVariationStatement
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)] : Prop :=
  ∃ (openRegion closedRegion : GlobalRegion X),
    RegionAdmCorrect X mu (integralReference X) openRegion ∧
      RegionAdmCorrect X mu (integralReference X) closedRegion ∧
      (Quotient.mk (sameBadMassSetoid X mu) openRegion) ≠
        (Quotient.mk (sameBadMassSetoid X mu) closedRegion)

/-- Actual two-region variation. -/
theorem etaRegionAdmVariation_actual
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      ProperSpace (localFieldAt X v)) :
    EtaRegionAdmVariationStatement X mu := by
  letI : IsUltrametricDist (localFieldAt X (badPlace X)) :=
    hultra (badPlace X) (P6AdmRedesign.badPlace_isFinite X)
  letI : ProperSpace (localFieldAt X (badPlace X)) :=
    hproperFinite (badPlace X) (P6AdmRedesign.badPlace_isFinite X)
  let openLocal : PositiveFiniteRegion (localFieldAt X (badPlace X)) (mu (badPlace X)) :=
    openRegion (K := localFieldAt X (badPlace X)) (mu := mu (badPlace X))
  let closedLocal : PositiveFiniteRegion (localFieldAt X (badPlace X)) (mu (badPlace X)) :=
    closedRegion (K := localFieldAt X (badPlace X)) (mu := mu (badPlace X))
  have openAdm : RegionAdmCorrect X mu (integralReference X) (openGlobalRegion X) := by
    refine {
      finiteSupport := ?_
      reference_measurable := ?_
      reference_pos := ?_
      reference_finite := ?_
      region_measurable := ?_
      region_pos := ?_
      region_finite := ?_ }
    · refine ⟨{badPlace X}, ?_⟩
      intro v hv
      unfold openGlobalRegion
      rw [if_neg (by simpa using hv)]
    · intro v; exact integralReference_measurable X hultra v
    · intro v; exact integralReference_pos X mu hultra v
    · intro v; exact integralReference_finite X mu hultra v
    · intro v
      by_cases hv : v = badPlace X
      · subst hv
        simpa [openGlobalRegion, openLocal, openRegion] using openLocal.measurable
      · rw [openGlobalRegion, if_neg hv]
        exact integralReference_measurable X hultra v
    · intro v
      by_cases hv : v = badPlace X
      · subst hv
        simpa [openGlobalRegion, openLocal, openRegion] using openLocal.pos
      · rw [openGlobalRegion, if_neg hv]
        exact integralReference_pos X mu hultra v
    · intro v
      by_cases hv : v = badPlace X
      · subst hv
        simpa [openGlobalRegion, openLocal, openRegion] using openLocal.finite
      · rw [openGlobalRegion, if_neg hv]
        exact integralReference_finite X mu hultra v
  have closedAdm : RegionAdmCorrect X mu (integralReference X) (closedGlobalRegion X) := by
    refine {
      finiteSupport := ?_
      reference_measurable := ?_
      reference_pos := ?_
      reference_finite := ?_
      region_measurable := ?_
      region_pos := ?_
      region_finite := ?_ }
    · refine ⟨{badPlace X}, ?_⟩
      intro v hv
      unfold closedGlobalRegion
      rw [if_neg (by simpa using hv)]
    · intro v; exact integralReference_measurable X hultra v
    · intro v; exact integralReference_pos X mu hultra v
    · intro v; exact integralReference_finite X mu hultra v
    · intro v
      by_cases hv : v = badPlace X
      · subst hv
        simpa [closedGlobalRegion, closedLocal, closedRegion] using closedLocal.measurable
      · rw [closedGlobalRegion, if_neg hv]
        exact integralReference_measurable X hultra v
    · intro v
      by_cases hv : v = badPlace X
      · subst hv
        simpa [closedGlobalRegion, closedLocal, closedRegion] using closedLocal.pos
      · rw [closedGlobalRegion, if_neg hv]
        exact integralReference_pos X mu hultra v
    · intro v
      by_cases hv : v = badPlace X
      · subst hv
        simpa [closedGlobalRegion, closedLocal, closedRegion] using closedLocal.finite
      · rw [closedGlobalRegion, if_neg hv]
        exact integralReference_finite X mu hultra v
  have hclasses :
      (Quotient.mk (sameBadMassSetoid X mu) (openGlobalRegion X)) ≠
        (Quotient.mk (sameBadMassSetoid X mu) (closedGlobalRegion X)) := by
    intro h
    have hrel : SameBadMass X mu (openGlobalRegion X) (closedGlobalRegion X) :=
      Quotient.exact h
    have hmass : mu (badPlace X) (openGlobalRegion X (badPlace X)) <
        mu (badPlace X) (closedGlobalRegion X (badPlace X)) := by
      simpa [openGlobalRegion, closedGlobalRegion, openLocal, closedLocal, openRegion, closedRegion]
        using open_mass_lt_closed_mass (K := localFieldAt X (badPlace X))
          (mu := mu (badPlace X))
    exact (ne_of_lt hmass) hrel
  exact ⟨openGlobalRegion X, closedGlobalRegion X, openAdm, closedAdm, hclasses⟩

/-- The two actual varying regions give distinct classes. -/
theorem varyingRegion_classes_ne
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      ProperSpace (localFieldAt X v)) :
    (Quotient.mk (sameBadMassSetoid X mu) (openGlobalRegion X)) ≠
      (Quotient.mk (sameBadMassSetoid X mu) (closedGlobalRegion X)) := by
  letI : IsUltrametricDist (localFieldAt X (badPlace X)) :=
    hultra (badPlace X) (P6AdmRedesign.badPlace_isFinite X)
  letI : ProperSpace (localFieldAt X (badPlace X)) :=
    hproperFinite (badPlace X) (P6AdmRedesign.badPlace_isFinite X)
  let openLocal : PositiveFiniteRegion (localFieldAt X (badPlace X)) (mu (badPlace X)) :=
    openRegion (K := localFieldAt X (badPlace X)) (mu := mu (badPlace X))
  let closedLocal : PositiveFiniteRegion (localFieldAt X (badPlace X)) (mu (badPlace X)) :=
    closedRegion (K := localFieldAt X (badPlace X)) (mu := mu (badPlace X))
  intro h
  have hrel : SameBadMass X mu (openGlobalRegion X) (closedGlobalRegion X) :=
    Quotient.exact h
  have hmass : mu (badPlace X) (openGlobalRegion X (badPlace X)) <
      mu (badPlace X) (closedGlobalRegion X (badPlace X)) := by
    simpa [openGlobalRegion, closedGlobalRegion, openLocal, closedLocal,
      openRegion, closedRegion]
      using open_mass_lt_closed_mass (K := localFieldAt X (badPlace X))
        (mu := mu (badPlace X))
  exact (ne_of_lt hmass) hrel

end LeanFormal.IUT.N8Closure.EtaRegionAdmVariation