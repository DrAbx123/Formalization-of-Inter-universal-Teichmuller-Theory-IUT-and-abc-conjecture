import tmp.sheaf.n8.closure.P6RelaxedNondegenerateReadout

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRssNontrivialActual

universe u

open MeasureTheory BigOperators Set
open LeanFormal.IUT.N8Closure.P6RelaxedNondegenerateReadout

variable {K : Type u} [NormedField K] [MeasurableSpace K] [BorelSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable (mu : Measure K) [Measure.IsAddHaarMeasure mu]

/-- Positive finite measurable regions in an actual nonarch local field. -/
structure PositiveFiniteRegion (K : Type u) [NormedField K] [MeasurableSpace K]
    (mu : Measure K) [Measure.IsAddHaarMeasure mu] where
  carrier : Set K
  measurable : MeasurableSet carrier
  pos : 0 < mu carrier
  finite : mu carrier < ⊤

/-- Equal-volume relation on positive finite regions. -/
def SameVolume : Setoid (PositiveFiniteRegion K mu) where
  r A B := mu A.carrier = mu B.carrier
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro A; rfl
    · intro A B h; exact h.symm
    · intro A B C hAB hBC; exact hAB.trans hBC

/-- The actual equal-volume quotient Rss. -/
abbrev Rss : Type _ := Quotient (SameVolume (K := K) mu)

/-- Actual closed unit ball as a positive finite region. -/
noncomputable def closedRegion : PositiveFiniteRegion K mu where
  carrier := Metric.closedBall (0 : K) 1
  measurable := Metric.isClosed_closedBall.measurableSet
  pos := lt_of_lt_of_le (Metric.measure_ball_pos mu 0 zero_lt_one)
    (measure_mono Metric.ball_subset_closedBall)
  finite := (isCompact_closedBall (0 : K) 1).measure_lt_top

/-- Actual open unit ball as a positive finite region. -/
noncomputable def openRegion : PositiveFiniteRegion K mu where
  carrier := Metric.ball (0 : K) 1
  measurable := measurableSet_ball
  pos := Metric.measure_ball_pos mu 0 zero_lt_one
  finite := lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
    (isCompact_closedBall (0 : K) 1).measure_lt_top

theorem open_mass_lt_closed_mass :
    mu (openRegion (K := K) mu).carrier <
      mu (closedRegion (K := K) mu).carrier :=
  ball_mass_lt_closedBall_mass (K := K) (muK := mu)

theorem open_mass_ne_closed_mass :
    mu (openRegion (K := K) mu).carrier ≠
      mu (closedRegion (K := K) mu).carrier :=
  ne_of_lt (open_mass_lt_closed_mass (K := K) (mu := mu))

/-- Two distinct equal-volume classes from actual closed/open balls. -/
theorem etaRss_quotient_classes_ne :
    (Quotient.mk (SameVolume (K := K) mu) (openRegion (K := K) mu)) ≠
      (Quotient.mk (SameVolume (K := K) mu) (closedRegion (K := K) mu)) := by
  intro h
  have hrel : SameVolume (K := K) mu (openRegion (K := K) mu)
      (closedRegion (K := K) mu) := Quotient.exact h
  exact open_mass_ne_closed_mass (K := K) (mu := mu) hrel

theorem etaRss_nontrivial : Nontrivial (Rss (K := K) mu) :=
  ⟨Quotient.mk (SameVolume (K := K) mu) (openRegion (K := K) mu),
    Quotient.mk (SameVolume (K := K) mu) (closedRegion (K := K) mu),
    etaRss_quotient_classes_ne (K := K) (mu := mu)⟩

/-- Log-volume readout on the equal-volume quotient. -/
noncomputable def logVolumeReadout : Rss (K := K) mu → ℝ :=
  Quotient.lift (fun A : PositiveFiniteRegion K mu =>
    Real.log (mu A.carrier).toReal) (by
      intro A B h
      exact congrArg (fun x : ENNReal => Real.log x.toReal) h)

theorem logVolumeReadout_mk (A : PositiveFiniteRegion K mu) :
    logVolumeReadout (K := K) (mu := mu)
      (Quotient.mk (SameVolume (K := K) mu) A) =
      Real.log (mu A.carrier).toReal := rfl

/-- The readout differs on the two actual classes. -/
theorem etaRss_readout_ne :
    logVolumeReadout (K := K) (mu := mu)
        (Quotient.mk (SameVolume (K := K) mu) (openRegion (K := K) mu)) ≠
      logVolumeReadout (K := K) (mu := mu)
        (Quotient.mk (SameVolume (K := K) mu) (closedRegion (K := K) mu)) := by
  intro h
  rw [logVolumeReadout_mk, logVolumeReadout_mk] at h
  have hposOpen : 0 < (mu (openRegion (K := K) mu).carrier).toReal :=
    ENNReal.toReal_pos (openRegion (K := K) mu).pos.ne'
      (openRegion (K := K) mu).finite.ne
  have hposClosed : 0 < (mu (closedRegion (K := K) mu).carrier).toReal :=
    ENNReal.toReal_pos (closedRegion (K := K) mu).pos.ne'
      (closedRegion (K := K) mu).finite.ne
  have hEq : (mu (openRegion (K := K) mu).carrier).toReal =
      (mu (closedRegion (K := K) mu).carrier).toReal :=
    Real.log_injOn_pos hposOpen hposClosed h
  exact open_mass_ne_closed_mass (K := K) (mu := mu)
    ((ENNReal.toReal_eq_toReal_iff' (openRegion (K := K) mu).finite.ne
      (closedRegion (K := K) mu).finite.ne).mp hEq)

end LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
