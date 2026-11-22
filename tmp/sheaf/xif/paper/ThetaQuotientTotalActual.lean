import tmp.sheaf.xif.paper.ThetaAutomorphyActual

/-!
# Actual total space of the quotient theta line bundle

Using the actual period Setoid and automorphy factor cocycle from
ThetaAutomorphyActual, this file constructs the total space

  total = Quot (period relation on Lˣ × L)

of the quotient line bundle, the projection to the actual period quotient
thetaPeriodBase, the fiber, and the theta section induced by oddTheta.

The relation is

  (U, c) ~ (r^a U, thetaAutomorphyFactor D a U * c).

Reflexivity uses factor 1, symmetry uses the inverse exponent and the factor
inverse (from the cocycle), and transitivity uses the actual factor cocycle.
The section [(U, oddTheta q U)] is well defined by the actual theta shift law
and satisfies the induced transformation law.

No source curve comparison is made and no inequality is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ABCBridge.ThetaQuotientTotalActual

open LeanFormal.IUT.Foundations.Theta

universe u

/-- The total quotient relation on Lˣ × L. -/
def thetaTotalRel {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (x y : Lˣ × L) : Prop :=
  ∃ a : ℤ,
    y.1 = (thetaRootUnit D) ^ a * x.1 ∧
    y.2 = thetaAutomorphyFactor D a (x.1 : L) * x.2

/-- The total quotient relation is an equivalence relation. -/
theorem thetaTotalRel_equivalence {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : Equivalence (thetaTotalRel D) where
  refl x := by
    refine ⟨0, ?_, ?_⟩
    · simp [thetaRootUnit]
    · simp [thetaAutomorphyFactor]
  symm := by
    rintro ⟨U, c⟩ ⟨V, d⟩ ⟨a, hV, hd⟩
    refine ⟨-a, ?_, ?_⟩
    · rw [hV]
      rw [zpow_neg]
      group
    · rw [hd]
      have hcoc := thetaAutomorphyFactor_cocycle D (U : L) (Units.ne_zero U) (-a) a
      have hzero : thetaAutomorphyFactor D ((-a) + a) (U : L) = 1 := by
        rw [neg_add_cancel]
        exact thetaAutomorphyFactor_zero D (U : L)
      rw [hzero] at hcoc
      rw [← hV] at hcoc
      calc
        c = 1 * c := by ring
        _ = (thetaAutomorphyFactor D (-a) (V : L) *
              thetaAutomorphyFactor D a (U : L)) * c := by rw [hcoc]
        _ = thetaAutomorphyFactor D (-a) (V : L) *
              (thetaAutomorphyFactor D a (U : L) * c) := by ring
  trans := by
    rintro ⟨U, c⟩ ⟨V, d⟩ ⟨W, e⟩ ⟨a, hV, hd⟩ ⟨b, hW, he⟩
    refine ⟨a + b, ?_, ?_⟩
    · rw [hW, hV]
      rw [zpow_add]
      group
    · rw [he, hd]
      have hcoc := thetaAutomorphyFactor_cocycle D (U : L) (Units.ne_zero U) b a
      rw [add_comm] at hcoc
      rw [← hV] at hcoc
      calc
        thetaAutomorphyFactor D b (V : L) *
            (thetaAutomorphyFactor D a (U : L) * c) =
          (thetaAutomorphyFactor D b (V : L) *
            thetaAutomorphyFactor D a (U : L)) * c := by ring
        _ = thetaAutomorphyFactor D (a + b) (U : L) * c := by rw [hcoc]

/-- The total quotient Setoid. -/
def thetaTotalSetoid {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : Setoid (Lˣ × L) :=
  ⟨thetaTotalRel D, thetaTotalRel_equivalence D⟩

/-- The actual total space of the quotient theta line bundle. -/
def thetaQuotientTotal {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : Type u :=
  Quot (thetaTotalSetoid D)

/-- Projection from the total space to the actual period quotient base. -/
def thetaQuotientProjection {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) :
    thetaQuotientTotal D → thetaPeriodBase D :=
  Quot.lift
    (fun x : Lˣ × L => Quot.mk (thetaPeriodSetoid D) x.1)
    (by
      intro x y h
      rcases h with ⟨a, hV, _hd⟩
      exact Quot.sound ⟨a, hV⟩)

/-- Fiber of the quotient theta line bundle. -/
def thetaQuotientFiber {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (_b : thetaPeriodBase D) : Type u :=
  L

/-- The projectivized total space structure. -/
structure ThetaQuotientTotalBundle
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) where
  base : Type u
  total : Type u
  projection : total → base
  fiber : base → Type u
  section : base → total

/-- Actual quotient total bundle object. -/
noncomputable def thetaQuotientTotalBundle {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : ThetaQuotientTotalBundle D where
  base := thetaPeriodBase D
  total := thetaQuotientTotal D
  projection := thetaQuotientProjection D
  fiber := thetaQuotientFiber D
  section := by
    intro b
    exact Quot.lift
      (fun U : Lˣ => Quot.mk (thetaTotalSetoid D) (U, oddTheta D.q (U : L)))
      (by
        intro U V h
        rcases h with ⟨a, hV, _hd⟩
        apply Quot.sound
        refine ⟨a, hV, ?_⟩
        rw [hV]
        exact thetaAutomorphy_shift D (U : L) (Units.ne_zero U) a)
      b

/-- The actual quotient section, on representatives of the period quotient. -/
theorem thetaQuotientSection_mk {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : Lˣ) :
    (thetaQuotientTotalBundle D).section
        (Quot.mk (thetaPeriodSetoid D) U) =
      Quot.mk (thetaTotalSetoid D) (U, oddTheta D.q (U : L)) :=
  rfl

/-- The section transformation law on representatives: the quotient section at
r^a U is the total class of the original section multiplied by the actual
automorphy factor. -/
theorem thetaQuotientSection_transformation
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (a : ℤ) (U : Lˣ) :
    (thetaQuotientTotalBundle D).section
        (Quot.mk (thetaPeriodSetoid D) ((thetaRootUnit D) ^ a * U)) =
      Quot.mk (thetaTotalSetoid D)
        (((thetaRootUnit D) ^ a * U),
          thetaAutomorphyFactor D a (U : L) * oddTheta D.q (U : L)) := by
  rw [thetaQuotientSection_mk]
  apply congrArg (Quot.mk (thetaTotalSetoid D))
  apply Prod.ext
  · rfl
  · exact thetaAutomorphy_shift D (U : L) (Units.ne_zero U) a

end ABCBridge.ThetaQuotientTotalActual

end
