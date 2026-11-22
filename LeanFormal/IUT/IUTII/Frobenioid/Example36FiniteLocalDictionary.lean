import LeanFormal.IUT.IUTII.Frobenioid.LocalFractionalIdealUnitQuotient
import LeanFormal.IUT.IUTII.Frobenioid.FinitePlaceFractionalIdealUnitQuotient

/-!
# The finite nonarchimedean local dictionary of IUT III, Example 3.6

This file packages the generator dictionary of the nonarchimedean half of
IUT III, Example 3.6.  It builds directly on
`LocalFractionalIdealUnitQuotient` and `FinitePlaceFractionalIdealUnitQuotient`:
the actual local dictionary `Kˣ / integralUnitImage ≃ (FractionalIdeal R⁰ K)ˣ`,
the principal-ideal surjectivity, the integral-unit action on genuine generators,
and the completion at an actual finite place are all imported, not reproved.

What is proved here:

* the action of integral units on the actual generators of a fixed fractional
  ideal is associative with a genuine identity element;
* the action is free and transitive, so a chosen generator is a base point and
  the chart `Rˣ ≃ Generators R K I` is bijective;
* the base-point change formula: if a new base point is `y = w • x`, then for
  every integral unit `u` one has `u • y = (u * w) • x`, and the coordinate of
  a generator with respect to the new base point is the old coordinate
  multiplied by `w⁻¹` (the convention of the handoff: changing the base point
  `a₀ ↦ w·a₀` multiplies coordinates by `w⁻¹`);
* the unique integral unit relating two generators of the same ideal, restated
  in the generator form used by the dictionary;
* a structure `GeneratorTorsor` bundling a base generator with its chart and
  the free/transitive/action laws, together with its canonical construction at
  a principal ideal domain;
* the specialization of all of this at the actual completion
  `v.adicCompletionIntegers K / v.adicCompletion K` of a finite place `v`,
  using the existing proved completion instances.

This is the local nonarchimedean construction only.  It does not construct the
global Frobenioid category, the global divisor/ideal families, or a source Hodge
theater; it does not supply the source theta generator or any landing statement
for it.  The archimedean half of Example 3.6 is a separate construction and is
not treated here.
-/

noncomputable section

open scoped nonZeroDivisors

namespace LeanFormal.IUT.Example36FiniteLocalDictionary

open LocalFractionalIdealUnitQuotient

variable (R K : Type*) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-! ### The integral-unit action on genuine generators -/

/-- The value of the integral-unit action on a generator: the action multiplies the
unit `x : Kˣ` representing the generator by the image of the integral unit. -/
@[simp]
theorem integralUnitMulGenerator_val {I : (FractionalIdeal R⁰ K)ˣ}
    (x : Generators R K I) (u : Rˣ) :
    (integralUnitMulGenerator R K x u).val =
      Units.map (algebraMap R K).toMonoidHom u * x.val := rfl

/-- The integral unit `1` acts trivially on genuine generators. -/
@[simp]
theorem integralUnitMulGenerator_one {I : (FractionalIdeal R⁰ K)ˣ}
    (x : Generators R K I) :
    integralUnitMulGenerator R K x (1 : Rˣ) = x := by
  apply Subtype.ext
  simp [integralUnitMulGenerator]

/-- The action law of integral units on genuine generators: acting by `u` after
acting by `v` is acting by the product `u * v`.  This is the associativity law
matching `integralUnitMulGenerator x u = u · x`. -/
@[simp]
theorem integralUnitMulGenerator_mul {I : (FractionalIdeal R⁰ K)ˣ}
    (x : Generators R K I) (u v : Rˣ) :
    integralUnitMulGenerator R K (integralUnitMulGenerator R K x v) u =
      integralUnitMulGenerator R K x (u * v) := by
  apply Subtype.ext
  simp only [integralUnitMulGenerator, map_mul, mul_assoc]

/-- The chart of a generator sends `1` to that generator. -/
@[simp]
theorem generatorChart_one {I : (FractionalIdeal R⁰ K)ˣ}
    (x : Generators R K I) : generatorChart R K x (1 : Rˣ) = x :=
  integralUnitMulGenerator_one R K x

/-! ### Freeness and transitivity -/

/-- The integral-unit action on the generators of a fixed fractional ideal is
injective: two integral units giving the same generator are equal. -/
theorem integralUnitMulGenerator_injective {I : (FractionalIdeal R⁰ K)ˣ}
    (x : Generators R K I) :
    Function.Injective (fun u : Rˣ => integralUnitMulGenerator R K x u) := by
  intro u v h
  have hval : Units.map (algebraMap R K).toMonoidHom u * x.val =
      Units.map (algebraMap R K).toMonoidHom v * x.val := congrArg Subtype.val h
  have hmap : Units.map (algebraMap R K).toMonoidHom u =
      Units.map (algebraMap R K).toMonoidHom v :=
    mul_right_cancel (b := x.val) (by simpa using hval)
  apply Units.ext
  apply IsFractionRing.injective R K
  have hcoe := congrArg (fun z : Kˣ => (z : K)) hmap
  simpa using hcoe

/-- Equality of two integral-unit translates of one generator is exactly equality of
the integral units. -/
theorem integralUnitMulGenerator_eq_iff {I : (FractionalIdeal R⁰ K)ˣ}
    (x : Generators R K I) (u v : Rˣ) :
    integralUnitMulGenerator R K x u = integralUnitMulGenerator R K x v ↔ u = v :=
  ⟨fun h => integralUnitMulGenerator_injective R K x h, fun h => by rw [h]⟩

/-- Freeness: an integral unit fixes a generator if and only if it is `1`. -/
theorem integralUnitMulGenerator_eq_self_iff {I : (FractionalIdeal R⁰ K)ˣ}
    (x : Generators R K I) (u : Rˣ) :
    integralUnitMulGenerator R K x u = x ↔ u = 1 := by
  constructor
  · intro h
    have hfix : integralUnitMulGenerator R K x u = integralUnitMulGenerator R K x 1 := by
      rwa [integralUnitMulGenerator_one]
    exact (integralUnitMulGenerator_eq_iff R K x u 1).mp hfix
  · rintro rfl
    exact integralUnitMulGenerator_one R K x

/-- Transitivity: every generator of a fixed fractional ideal is an integral-unit
translate of any other chosen generator. -/
theorem exists_integralUnitMulGenerator_eq {I : (FractionalIdeal R⁰ K)ˣ}
    (x y : Generators R K I) :
    ∃ u : Rˣ, y = integralUnitMulGenerator R K x u := by
  obtain ⟨u, hu⟩ := (generatorChart R K x).surjective y
  exact ⟨u, by rw [← hu]; rfl⟩

/-- Transitivity with uniqueness: the integral unit translating `x` to `y` is
unique.  This is the free-and-transitive torsor law of the generator dictionary. -/
theorem existsUnique_integralUnitMulGenerator_eq {I : (FractionalIdeal R⁰ K)ˣ}
    (x y : Generators R K I) :
    ∃! u : Rˣ, y = integralUnitMulGenerator R K x u := by
  obtain ⟨u, hu⟩ := (generatorChart R K x).surjective y
  refine ⟨u, by rw [← hu]; rfl, ?_⟩
  intro v hv
  have hgen : integralUnitMulGenerator R K x v = integralUnitMulGenerator R K x u := by
    rw [← hv, ← hu]
    rfl
  exact (integralUnitMulGenerator_eq_iff R K x v u).mp hgen

/-- The integral unit relating two generators, in the chapter's generator form:
equality of the actual principal ideals is equivalent to the existence of a unique
integral unit carrying one generator to the other.  This is the imported theorem
`principalIdeal_eq_iff_existsUnique_integralUnit` read on generators. -/
theorem toPrincipalIdeal_eq_iff_existsUnique_integralUnit_generators
    {I : (FractionalIdeal R⁰ K)ˣ} (x y : Generators R K I) :
    (toPrincipalIdeal R K x.val = toPrincipalIdeal R K y.val) ↔
      ∃! u : Rˣ, Units.map (algebraMap R K).toMonoidHom u * x.val = y.val :=
  principalIdeal_eq_iff_existsUnique_integralUnit R K x.val y.val

/-- Two generators of the same fractional ideal are related by a unique integral
unit. -/
theorem existsUnique_relating_integralUnit {I : (FractionalIdeal R⁰ K)ˣ}
    (x y : Generators R K I) :
    ∃! u : Rˣ, Units.map (algebraMap R K).toMonoidHom u * x.val = y.val := by
  have h : (toPrincipalIdeal R K) x.val = (toPrincipalIdeal R K) y.val :=
    x.property.trans y.property.symm
  exact (toPrincipalIdeal_eq_iff_existsUnique_integralUnit_generators R K x y).mp h

/-! ### Base-point change -/

/-- Base-point change formula.  If the new base point is `y = w • x`, then acting
on `y` by the integral unit `u` is the same as acting on the old base point `x`
by `u * w`.  Equivalently, in coordinates: changing the base point
`x ↦ w · x` multiplies the old coordinate `u` by `w⁻¹`. -/
theorem integralUnitMulGenerator_baseChange
    {I : (FractionalIdeal R⁰ K)ˣ} {x y : Generators R K I} {w : Rˣ}
    (hy : y = integralUnitMulGenerator R K x w) (u : Rˣ) :
    integralUnitMulGenerator R K y u = integralUnitMulGenerator R K x (u * w) := by
  rw [hy]
  exact integralUnitMulGenerator_mul R K x u w

/-- The coordinate form of base-point change: if `y = w • x`, then the coordinate
of a generator `z` with respect to the new base point `y` is its coordinate with
respect to `x` multiplied by `w⁻¹`. -/
theorem generatorChart_symm_baseChange
    {I : (FractionalIdeal R⁰ K)ˣ} {x y : Generators R K I} {w : Rˣ}
    (hy : y = integralUnitMulGenerator R K x w) (z : Generators R K I) :
    (generatorChart R K y).symm z = (generatorChart R K x).symm z * w⁻¹ := by
  obtain ⟨u, rfl⟩ : ∃ u : Rˣ, z = integralUnitMulGenerator R K x u :=
    exists_integralUnitMulGenerator_eq R K x z
  have hmul : integralUnitMulGenerator R K y (u * w⁻¹) =
      integralUnitMulGenerator R K x u := by
    rw [integralUnitMulGenerator_baseChange R K hy (u * w⁻¹)]
    congr 1
    simp
  have hleft : (generatorChart R K y).symm (integralUnitMulGenerator R K x u) = u * w⁻¹ := by
    rw [Equiv.symm_apply_eq]
    rw [show (generatorChart R K y) (u * w⁻¹) =
      integralUnitMulGenerator R K y (u * w⁻¹) from rfl]
    exact hmul.symm
  have hright : (generatorChart R K x).symm (integralUnitMulGenerator R K x u) = u :=
    (generatorChart R K x).symm_apply_apply u
  rw [hleft, hright]

/-! ### The generator torsor -/

/-- A choice of base generator of a fixed fractional ideal, together with the
resulting chart identifying the integral-unit group with the whole generator set.
The chart is required to be the canonical one, so the free, transitive and
base-point-change laws below are the actual action laws, not extra hypotheses. -/
structure GeneratorTorsor (I : (FractionalIdeal R⁰ K)ˣ) where
  /-- A chosen base generator of the fractional ideal. -/
  base : Generators R K I
  /-- The chart of the torsor: integral units identify with all generators. -/
  chart : Rˣ ≃ Generators R K I
  /-- The chart is the canonical action chart at the base generator. -/
  chart_apply : ∀ u : Rˣ, chart u = integralUnitMulGenerator R K base u

namespace GeneratorTorsor

variable {R K} {I : (FractionalIdeal R⁰ K)ˣ}

/-- The chart of a torsor is the canonical action chart of its base generator. -/
theorem chart_eq (T : GeneratorTorsor R K I) (u : Rˣ) :
    T.chart u = integralUnitMulGenerator R K T.base u :=
  T.chart_apply u

/-- The chart of a torsor is injective. -/
theorem chart_injective (T : GeneratorTorsor R K I) : Function.Injective T.chart :=
  T.chart.injective

/-- The chart of a torsor is surjective. -/
theorem chart_surjective (T : GeneratorTorsor R K I) : Function.Surjective T.chart :=
  T.chart.surjective

/-- Freeness for the packaged torsor chart. -/
theorem free (T : GeneratorTorsor R K I) (u v : Rˣ) :
    T.chart u = T.chart v ↔ u = v :=
  T.chart.injective.eq_iff

/-- The trivial integral unit is the base generator. -/
@[simp]
theorem chart_one (T : GeneratorTorsor R K I) : T.chart 1 = T.base := by
  rw [T.chart_eq]
  exact integralUnitMulGenerator_one R K T.base

/-- A chart value is the base generator if and only if the unit is trivial. -/
theorem eq_base_iff (T : GeneratorTorsor R K I) (u : Rˣ) :
    T.chart u = T.base ↔ u = 1 := by
  rw [← T.chart_one, T.free]

/-- The action law expressed through the chart: acting on the generator `T.chart v`
by `u` gives the generator with coordinate `u * v`. -/
theorem chart_mul (T : GeneratorTorsor R K I) (u v : Rˣ) :
    integralUnitMulGenerator R K (T.chart v) u = T.chart (u * v) := by
  rw [T.chart_eq v, T.chart_eq (u * v)]
  exact integralUnitMulGenerator_mul R K T.base u v

/-- Transitivity for the packaged torsor: every generator has some coordinate. -/
theorem exists_coordinate (T : GeneratorTorsor R K I) (y : Generators R K I) :
    ∃ u : Rˣ, y = T.chart u := by
  obtain ⟨u, hu⟩ := T.chart.surjective y
  exact ⟨u, hu.symm⟩

/-- Every generator has a unique integral-unit coordinate in the packaged torsor. -/
theorem existsUnique_coordinate (T : GeneratorTorsor R K I) (y : Generators R K I) :
    ∃! u : Rˣ, y = T.chart u := by
  obtain ⟨u, hu⟩ := T.exists_coordinate y
  exact ⟨u, hu, fun v hv => (T.free v u).mp (hv.symm.trans hu)⟩

/-- The unique integral unit relating the base generator to any other generator,
stated multiplicatively. -/
theorem existsUnique_integralUnit_mul_base (T : GeneratorTorsor R K I)
    (y : Generators R K I) :
    ∃! u : Rˣ, Units.map (algebraMap R K).toMonoidHom u * T.base.val = y.val :=
  existsUnique_relating_integralUnit R K T.base y

/-- The integral-unit action on the torsor, transported through its chart: the
coordinate of the result is the product `u * v` of the acting unit and the
coordinate `v` of the acted generator. -/
def act (T : GeneratorTorsor R K I) (u : Rˣ) (y : Generators R K I) :
    Generators R K I :=
  T.chart (u * T.chart.symm y)

/-- The transported chart action is the actual integral-unit action on genuine
generators, so the transport does not change the dictionary. -/
theorem act_eq_integralUnitMulGenerator (T : GeneratorTorsor R K I) (u : Rˣ)
    (y : Generators R K I) :
    T.act u y = integralUnitMulGenerator R K y u := by
  calc
    T.act u y = integralUnitMulGenerator R K T.base (u * T.chart.symm y) :=
      T.chart_eq (u * T.chart.symm y)
    _ = integralUnitMulGenerator R K
          (integralUnitMulGenerator R K T.base (T.chart.symm y)) u :=
      (integralUnitMulGenerator_mul R K T.base u (T.chart.symm y)).symm
    _ = integralUnitMulGenerator R K (T.chart (T.chart.symm y)) u := by
      rw [← T.chart_eq (T.chart.symm y)]
    _ = integralUnitMulGenerator R K y u := by rw [T.chart.apply_symm_apply]

/-- The transported action has a genuine identity element. -/
@[simp]
theorem act_one (T : GeneratorTorsor R K I) (y : Generators R K I) :
    T.act 1 y = y := by
  rw [act_eq_integralUnitMulGenerator]
  exact integralUnitMulGenerator_one R K y

/-- The transported action is associative: acting by `u * v` is acting by `u`
after acting by `v`. -/
theorem act_mul (T : GeneratorTorsor R K I) (u v : Rˣ) (y : Generators R K I) :
    T.act (u * v) y = T.act u (T.act v y) := by
  rw [act_eq_integralUnitMulGenerator, act_eq_integralUnitMulGenerator,
    act_eq_integralUnitMulGenerator]
  exact (integralUnitMulGenerator_mul R K y u v).symm

/-- A torsor based at an explicitly given generator. -/
noncomputable def ofBase (x : Generators R K I) : GeneratorTorsor R K I where
  base := x
  chart := generatorChart R K x
  chart_apply := fun _ => rfl

@[simp]
theorem ofBase_base (x : Generators R K I) : (ofBase x).base = x := rfl

@[simp]
theorem ofBase_chart_apply (x : Generators R K I) (u : Rˣ) :
    (ofBase x).chart u = integralUnitMulGenerator R K x u := rfl

/-- Base-point change for the packaged torsors: if `y = w • x`, then the chart of
the torsor based at `y` is the chart of the torsor based at `x` precomposed with
right multiplication by `w` on the integral-unit group. -/
theorem ofBase_chart_baseChange {x y : Generators R K I} {w : Rˣ}
    (hy : y = integralUnitMulGenerator R K x w) (u : Rˣ) :
    (ofBase y).chart u = (ofBase x).chart (u * w) :=
  integralUnitMulGenerator_baseChange R K hy u

/-- Coordinate form of the packaged base-point change: the coordinate of `z` with
respect to the new base point `y = w • x` is the old coordinate multiplied by
`w⁻¹`. -/
theorem ofBase_coordinate_baseChange {x y : Generators R K I} {w : Rˣ}
    (hy : y = integralUnitMulGenerator R K x w) (z : Generators R K I) :
    (ofBase y).chart.symm z = (ofBase x).chart.symm z * w⁻¹ :=
  generatorChart_symm_baseChange R K hy z

/-- The canonical generator torsor of a fractional ideal over a principal ideal
domain: the base generator is supplied by the imported principal-ideal
surjectivity, not assumed here. -/
noncomputable def ofIdeal [IsPrincipalIdealRing R] (I : (FractionalIdeal R⁰ K)ˣ) :
    GeneratorTorsor R K I :=
  ofBase (Classical.choice (generators_nonempty R K I))

end GeneratorTorsor

/-! ### Specialization to the actual completion at a finite place -/

section FinitePlace

variable (R K : Type*) [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (v : IsDedekindDomain.HeightOneSpectrum R)

/-- The canonical generator torsor, at the actual completion `v.adicCompletion K` of
a finite place, of an invertible fractional ideal of the completed valuation ring
`v.adicCompletionIntegers K`.  The principal ideal domain structure, the fraction
field structure, and the algebra structure of the completion are the imported
instances; no completion fact is reproved here. -/
noncomputable def completionGeneratorTorsor
    (I : (FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K))ˣ) :
    GeneratorTorsor (v.adicCompletionIntegers K) (v.adicCompletion K) I :=
  GeneratorTorsor.ofIdeal (R := v.adicCompletionIntegers K) (K := v.adicCompletion K) I

open LeanFormal.IUT.FinitePlaceFractionalIdealUnitQuotient

/-- Compatibility of the generator dictionary with the imported completed local unit
quotient dictionary of Example 3.6: under the completed dictionary, every generator
of a fixed invertible fractional ideal of the completed valuation ring has quotient
class equal to that ideal.  This is the point where the generator torsor is tied back
to the imported quotient identification. -/
theorem completionGenerator_quotientClass_eq
    (I : (FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K))ˣ)
    (x : Generators (v.adicCompletionIntegers K) (v.adicCompletion K) I) :
    completionUnitQuotientEquivFractionalIdeals R K v (QuotientGroup.mk x.val) = I := by
  change localUnitQuotientEquivFractionalIdeals (v.adicCompletionIntegers K) (v.adicCompletion K)
    (QuotientGroup.mk x.val) = I
  rw [localUnitQuotientEquivFractionalIdeals_mk]
  exact x.property

/-- Freeness of the integral-unit action at the actual completion. -/
theorem completionGeneratorTorsor_free
    (I : (FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K))ˣ)
    (u w : (v.adicCompletionIntegers K)ˣ) :
    (completionGeneratorTorsor R K v I).chart u =
        (completionGeneratorTorsor R K v I).chart w ↔ u = w :=
  GeneratorTorsor.free (completionGeneratorTorsor R K v I) u w

/-- Transitivity with uniqueness at the actual completion: every generator of a
fixed invertible fractional ideal has a unique integral-unit coordinate. -/
theorem completionGeneratorTorsor_existsUnique_coordinate
    (I : (FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K))ˣ)
    (y : Generators (v.adicCompletionIntegers K) (v.adicCompletion K) I) :
    ∃! u : (v.adicCompletionIntegers K)ˣ,
      y = (completionGeneratorTorsor R K v I).chart u :=
  GeneratorTorsor.existsUnique_coordinate (completionGeneratorTorsor R K v I) y

/-- The unique integral unit of the completed valuation ring relating two generators
of one invertible fractional ideal, in generator form. -/
theorem completion_existsUnique_relating_integralUnit
    (I : (FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K))ˣ)
    (x y : Generators (v.adicCompletionIntegers K) (v.adicCompletion K) I) :
    ∃! u : (v.adicCompletionIntegers K)ˣ,
      Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom u *
        x.val = y.val :=
  existsUnique_relating_integralUnit (v.adicCompletionIntegers K) (v.adicCompletion K) x y

/-- The generator form of the completed principal-ideal dictionary: equality of the
actual completed principal ideals is equivalent to the existence of a unique
integral unit of the completed valuation ring carrying one generator to the other. -/
theorem completion_toPrincipalIdeal_eq_iff_existsUnique_integralUnit_generators
    (I : (FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K))ˣ)
    (x y : Generators (v.adicCompletionIntegers K) (v.adicCompletion K) I) :
    (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) x.val =
        toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) y.val) ↔
      ∃! u : (v.adicCompletionIntegers K)ˣ,
        Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom u *
          x.val = y.val :=
  toPrincipalIdeal_eq_iff_existsUnique_integralUnit_generators
    (v.adicCompletionIntegers K) (v.adicCompletion K) x y

/-- Freeness at the actual completion: an integral unit of the completed valuation
ring fixes a generator if and only if it is trivial. -/
theorem completion_integralUnitMulGenerator_eq_self_iff
    (I : (FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K))ˣ)
    (x : Generators (v.adicCompletionIntegers K) (v.adicCompletion K) I)
    (u : (v.adicCompletionIntegers K)ˣ) :
    integralUnitMulGenerator (v.adicCompletionIntegers K) (v.adicCompletion K) x u = x ↔
      u = 1 :=
  integralUnitMulGenerator_eq_self_iff (v.adicCompletionIntegers K) (v.adicCompletion K) x u

/-- Base-point change at the actual completion: if the new base generator is
`w • x`, then acting by `u` on the new base point is acting by `u * w` on the old
one. -/
theorem completion_integralUnitMulGenerator_baseChange
    {I : (FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K))ˣ}
    {x y : Generators (v.adicCompletionIntegers K) (v.adicCompletion K) I}
    {w : (v.adicCompletionIntegers K)ˣ}
    (hy : y = integralUnitMulGenerator (v.adicCompletionIntegers K) (v.adicCompletion K) x w)
    (u : (v.adicCompletionIntegers K)ˣ) :
    integralUnitMulGenerator (v.adicCompletionIntegers K) (v.adicCompletion K) y u =
      integralUnitMulGenerator (v.adicCompletionIntegers K) (v.adicCompletion K) x (u * w) :=
  integralUnitMulGenerator_baseChange (v.adicCompletionIntegers K) (v.adicCompletion K) hy u

/-- Coordinate form of base-point change at the actual completion: changing the
base generator `x ↦ w · x` multiplies the coordinate of any generator by `w⁻¹`. -/
theorem completion_generatorChart_symm_baseChange
    {I : (FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K))ˣ}
    {x y : Generators (v.adicCompletionIntegers K) (v.adicCompletion K) I}
    {w : (v.adicCompletionIntegers K)ˣ}
    (hy : y = integralUnitMulGenerator (v.adicCompletionIntegers K) (v.adicCompletion K) x w)
    (z : Generators (v.adicCompletionIntegers K) (v.adicCompletion K) I) :
    (generatorChart (v.adicCompletionIntegers K) (v.adicCompletion K) y).symm z =
      (generatorChart (v.adicCompletionIntegers K) (v.adicCompletion K) x).symm z * w⁻¹ :=
  generatorChart_symm_baseChange (v.adicCompletionIntegers K) (v.adicCompletion K) hy z

end FinitePlace

end LeanFormal.IUT.Example36FiniteLocalDictionary
