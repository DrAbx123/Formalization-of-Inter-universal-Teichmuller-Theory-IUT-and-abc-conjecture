import tmp.sheaf.xif.paper.S2134D9DescentActual

/-!
# S2448: an actual non-split two-arrow etale cover and its amalgamation interface

The D9 effective-descent target of S2134 is proved there only for the base cases
"generated sieve maximal" (identity cover, split epimorphisms).  This file constructs,
at a *specific* scheme over the rationals, an actual etale cover from the precoverage
`S2093EtalePrecoverage ℚ` which is outside all those base cases, and records exactly
what its descent/amalgamation statement is.

## The concrete cover

The base is the two-point scheme

  `S = Spec ℚ ⨿ Spec ℚ`

regarded as a scheme over `Spec ℚ` through the codiagonal
`Spec ℚ ⨿ Spec ℚ ⟶ Spec ℚ`.  The cover is the two-arrow family of the coproduct
inclusions

  `Spec ℚ ⟶ Spec ℚ ⨿ Spec ℚ`   (first and second inclusion).

It is an actual etale precoverage cover: both arrows are open immersions (hence
etale) and their images are disjoint and jointly surjective.  It is *not* an
identity cover, its generated sieve is *not* maximal, and neither arrow is a split
epimorphism.  Hence none of the base-case theorems of S2134 applies.

## The amalgamation statement

The exact effective-descent/amalgamation statement at this cover is
`S2448ConcreteAmalgam`: every descent datum for the slice-sheaf prestack
`S2029SheafPrestack ℚ` on the cover has an amalgamation.  We prove:

* it is equivalent to essential surjectivity of the descent functor at the cover;
* it is implied by the general D9 effective-descent missing `S2134FirstMissing`;
* it is implied by `S2448EtaleAmalgamation`, the indexed-family form of the
  slice-sheaf amalgamation theorem on the D9 site (equivalently the effective
  descent form of `S2134FirstMissing`).

No amalgamation is constructed: the construction needs the Cech descent /
stack-of-slice-sheaves theorem, which Mathlib v4.32.2 does not contain (there is
no `Pseudofunctor.IsStack` instance for a category-valued pseudofunctor at all).
The file isolates this as the exact first missing for the concrete cover.  It
contains no `sorry`, no `axiom`, no `True`/`PUnit` carrier and no fabricated
stack instance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Limits
open scoped AlgebraicGeometry

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2448GeneralCoverActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual

universe u

/-! ## 1. The concrete scheme and the two-arrow family -/

/-- The concrete base field: the rationals. -/
abbrev K : Type := ℚ

/-- The one-point scheme `Spec ℚ`. -/
abbrev point : Scheme := Spec (CommRingCat.of K)

/-- The two-point scheme `Spec ℚ ⨿ Spec ℚ`, as an object of `SchemeOverField ℚ`
through the codiagonal. -/
def baseScheme : Iut.SchemeOverField K :=
  Over.mk (coprod.desc (𝟙 point) (𝟙 point))

/-- The common source of the two cover arrows: the terminal object of the slice over
`Spec ℚ`. -/
def coverObj (_ : Bool) : Iut.SchemeOverField K :=
  Over.mk (𝟙 point)

/-- The underlying scheme morphism of the first and second coproduct inclusion. -/
def coverMap (i : Bool) : point ⟶ point ⨿ point :=
  if i then (coprod.inr : point ⟶ point ⨿ point) else coprod.inl

/-- The two coproduct inclusions, as arrows in the slice over `Spec ℚ`. -/
def coverArrow (i : Bool) : coverObj i ⟶ baseScheme :=
  Over.homMk (coverMap i) (by
    cases i <;> simp [coverMap, baseScheme, coverObj])

/-- The concrete two-arrow presieve. -/
def coverPresieve : Presieve baseScheme :=
  Presieve.ofArrows coverObj coverArrow

/-! ## 2. The cover is an actual etale precoverage cover -/

/-- The concrete two-arrow family is an actual etale precoverage cover. -/
theorem coverPresieve_mem :
    coverPresieve ∈ (S2093EtalePrecoverage K).coverings baseScheme := by
  change coverPresieve.map (Over.forget (Spec (CommRingCat.of K))) ∈
    Scheme.etalePrecoverage ((Over.forget (Spec (CommRingCat.of K))).obj baseScheme)
  rw [show coverPresieve.map (Over.forget (Spec (CommRingCat.of K))) =
      Presieve.ofArrows (fun i : Bool => (coverObj i).left)
        (fun i : Bool => (coverArrow i).left) by
    simp [coverPresieve, Presieve.map_ofArrows]]
  change Presieve.ofArrows (fun _ : Bool => point) coverMap ∈
    Scheme.etalePrecoverage (point ⨿ point)
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)
    (S := point ⨿ point) (X := fun _ : Bool => point)
    (f := coverMap)).mpr ?_
  constructor
  · intro x
    have hcompl : IsCompl (Set.range (coprod.inl : point ⟶ point ⨿ point))
        (Set.range (coprod.inr : point ⟶ point ⨿ point)) :=
      isCompl_range_inl_inr point point
    have hx : x ∈ (Set.range (coprod.inl : point ⟶ point ⨿ point)) ⊔
        (Set.range (coprod.inr : point ⟶ point ⨿ point)) := by
      rw [hcompl.sup_eq_top]
      exact Set.mem_univ x
    simp only [Set.sup_eq_union, Set.mem_union] at hx
    rcases hx with hx | hx
    · exact ⟨false, by simpa [coverMap] using hx⟩
    · exact ⟨true, by simpa [coverMap] using hx⟩
  · intro i
    cases i <;> simp [coverMap] <;> infer_instance

/-! ## 3. The cover is outside the S2134 base cases -/

/-- The codiagonal followed by the first inclusion, written as
`coprod.desc coprod.inl coprod.inl`, is not the identity. -/
theorem codiag_comp_inl_ne_id :
    (coprod.desc (coprod.inl : point ⟶ point ⨿ point)
      (coprod.inl : point ⟶ point ⨿ point)) ≠ 𝟙 (point ⨿ point) := by
  intro h
  have h' : (coprod.inr : point ⟶ point ⨿ point) ≫
      (coprod.desc (coprod.inl : point ⟶ point ⨿ point)
        (coprod.inl : point ⟶ point ⨿ point)) =
      (coprod.inr : point ⟶ point ⨿ point) := by
    rw [h]
    simp
  rw [coprod.inr_desc] at h'
  have hinl : (coprod.inl : point ⟶ point ⨿ point) = coprod.inr := by
    simpa using h'
  exact absurd (congrArg (fun k => k (default : ↥point)) hinl)
    (inl_ne_inr (X := point) (Y := point) (default : ↥point) (default : ↥point))

/-- The codiagonal followed by the second inclusion is not the identity. -/
theorem codiag_comp_inr_ne_id :
    (coprod.desc (coprod.inr : point ⟶ point ⨿ point)
      (coprod.inr : point ⟶ point ⨿ point)) ≠ 𝟙 (point ⨿ point) := by
  intro h
  have h' : (coprod.inl : point ⟶ point ⨿ point) ≫
      (coprod.desc (coprod.inr : point ⟶ point ⨿ point)
        (coprod.inr : point ⟶ point ⨿ point)) =
      (coprod.inl : point ⟶ point ⨿ point) := by
    rw [h]
    simp
  rw [coprod.inl_desc] at h'
  have hinl : (coprod.inr : point ⟶ point ⨿ point) = coprod.inl := by
    simpa using h'
  exact absurd (congrArg (fun k => k (default : ↥point)) hinl)
    (inr_ne_inl (X := point) (Y := point) (default : ↥point) (default : ↥point))

/-- **The generated sieve of the concrete cover is proper.**  The identity arrow does not
factor through either coproduct inclusion: the only arrow from `baseScheme` to the
terminal object `coverObj i` is the structure morphism, and composing it with an
inclusion is not the identity. -/
theorem generate_coverPresieve_ne_top : Sieve.generate coverPresieve ≠ ⊤ := by
  intro htop
  have hid : Sieve.ofArrows coverObj coverArrow (𝟙 baseScheme) := by
    have htop' : (Sieve.ofArrows coverObj coverArrow) = (⊤ : Sieve baseScheme) := by
      simpa [coverPresieve] using htop
    rw [htop']
    trivial
  rw [Sieve.mem_ofArrows_iff] at hid
  obtain ⟨i, a, ha⟩ := hid
  have hterm : a = Over.mkIdTerminal.from baseScheme :=
    Over.mkIdTerminal.hom_ext a (Over.mkIdTerminal.from baseScheme)
  have hcomp : Over.mkIdTerminal.from baseScheme ≫ coverArrow i = 𝟙 baseScheme := by
    rw [← hterm]
    exact ha.symm
  have hleft : (Over.mkIdTerminal.from baseScheme).left ≫ (coverArrow i).left =
      𝟙 baseScheme.left := by
    simpa using congrArg Over.Hom.left hcomp
  rw [Over.mkIdTerminal_from_left] at hleft
  cases i
  · have h := hleft
    simp [coverArrow, baseScheme] at h
    exact codiag_comp_inl_ne_id h
  · have h := hleft
    simp [coverArrow, baseScheme] at h
    exact codiag_comp_inr_ne_id h

/-- The identity morphism is not in the concrete presieve. -/
theorem id_not_mem_coverPresieve : ¬ coverPresieve (𝟙 baseScheme) := by
  intro h
  haveI : IsSplitEpi (𝟙 baseScheme) := inferInstance
  exact generate_coverPresieve_ne_top
    (Sieve.generate_of_contains_isSplitEpi (𝟙 baseScheme) h)

/-- No arrow of the concrete cover is a split epimorphism. -/
theorem coverArrow_not_isSplitEpi (i : Bool) : ¬ IsSplitEpi (coverArrow i) := by
  intro h
  haveI : IsSplitEpi (coverArrow i) := h
  exact generate_coverPresieve_ne_top
    (Sieve.generate_of_contains_isSplitEpi (coverArrow i) (Presieve.ofArrows.mk i))

/-- The base-case hypotheses of S2134 fail simultaneously at the concrete cover. -/
theorem baseCase_hypotheses_fail :
    Sieve.generate coverPresieve ≠ ⊤ ∧ ∀ i : Bool, ¬ IsSplitEpi (coverArrow i) :=
  ⟨generate_coverPresieve_ne_top, coverArrow_not_isSplitEpi⟩

/-- The two arrows of the concrete cover are distinct: the first and second coproduct
inclusions are not equal. -/
theorem coverArrow_false_ne_true : coverArrow false ≠ coverArrow true := by
  intro h
  have hleft : coverMap false = coverMap true := by
    simpa [coverArrow] using congrArg Over.Hom.left h
  have hinl : (coprod.inl : point ⟶ point ⨿ point) = coprod.inr := by
    simpa [coverMap] using hleft
  exact absurd (congrArg (fun k => k (default : ↥point)) hinl)
    (inl_ne_inr (X := point) (Y := point) (default : ↥point) (default : ↥point))

/-- The concrete cover is not the singleton identity cover of S2134. -/
theorem coverPresieve_ne_singleton_id :
    coverPresieve ≠ Presieve.singleton (𝟙 baseScheme) := by
  intro h
  apply id_not_mem_coverPresieve
  rw [h]
  exact Presieve.singleton_self _

/-! ## 4. The exact amalgamation statement at the cover -/

/-- **The exact amalgamation statement for the concrete cover.**  Every descent datum
for the slice-sheaf prestack on the two-arrow cover has an amalgamation. -/
def S2448ConcreteAmalgam : Prop :=
  ∀ D : (S2029SheafPrestack K).DescentData
      (fun g : coverPresieve.category => g.obj.hom),
    Nonempty (Amalgam (S2029SheafPrestack K)
      (fun g : coverPresieve.category => g.obj.hom) D)

/-- The amalgamation statement is exactly essential surjectivity of the descent functor
at the concrete cover. -/
theorem concreteAmalgam_iff_effectiveDescent :
    S2448ConcreteAmalgam ↔
      HasEffectiveDescentPresieve (S2029SheafPrestack K) coverPresieve :=
  (hasEffectiveDescent_iff_amalgam (S2029SheafPrestack K)
    (fun g : coverPresieve.category => g.obj.hom)).symm

/-- The same statement with the original `Bool`-indexed family. -/
def S2448ConcreteAmalgamIndex : Prop :=
  ∀ D : (S2029SheafPrestack K).DescentData coverArrow,
    Nonempty (Amalgam (S2029SheafPrestack K) coverArrow D)

/-- The indexed form and the presieve form of the concrete amalgamation statement agree:
the two families generate the same sieve. -/
theorem concreteAmalgamIndex_iff :
    S2448ConcreteAmalgamIndex ↔ S2448ConcreteAmalgam := by
  unfold S2448ConcreteAmalgamIndex
  rw [← hasEffectiveDescent_iff_amalgam (S2029SheafPrestack K) coverArrow,
    concreteAmalgam_iff_effectiveDescent]
  exact hasEffectiveDescent_iff_of_sieve_eq (F := S2029SheafPrestack K)
    (f := coverArrow)
    (f' := fun g : coverPresieve.category => g.obj.hom) (by
      rw [Sieve.ofArrows_category']
      rfl)

/-- **The concrete amalgamation is exactly the effective-descent half of the stack
condition at the cover.**  The remaining half is the prestack (descent of morphisms)
condition at the cover, which is the S2103-type input. -/
theorem concreteStackFor_iff_prestack_and_amalgam :
    (S2029SheafPrestack K).IsStackFor coverPresieve ↔
      (S2029SheafPrestack K).IsPrestackFor coverPresieve ∧
        S2448ConcreteAmalgam := by
  rw [concreteAmalgam_iff_effectiveDescent]
  constructor
  · intro h
    exact ⟨h.isPrestackFor, h.essSurj⟩
  · rintro ⟨hP, hE⟩
    rw [Pseudofunctor.isStackFor_iff]
    exact Functor.IsEquivalence.mk hP.fullyFaithful.faithful
      hP.fullyFaithful.full hE

/-! ## 5. Reduction to the general missing theorem -/

/-- **The D9 amalgamation missing in the form matched to this file**: every descent datum
on every actual etale covering family of the D9 site has an amalgamation.  This is
exactly the amalgamation form of `S2134FirstMissing`. -/
def S2448EtaleAmalgamation (K : Type u) [Field K] : Prop :=
  ∀ (S : Iut.SchemeOverField K) (R : Presieve S),
    R ∈ (S2093EtalePrecoverage K).coverings S →
      ∀ D : (S2029SheafPrestack K).DescentData
          (fun g : R.category => g.obj.hom),
        Nonempty (Amalgam (S2029SheafPrestack K)
          (fun g : R.category => g.obj.hom) D)

/-- The amalgamation form is exactly the effective-descent form of S2134. -/
theorem etaleAmalgamation_iff_S2134 :
    S2448EtaleAmalgamation K ↔ S2134EffDescentOnEtaleFamilies (K := K) :=
  (S2134EffDescentOnEtaleFamilies_iff_amalgam (K := K)).symm

/-- **The general D9 missing implies the concrete amalgamation statement.** -/
theorem concreteAmalgam_of_etaleAmalgamation
    (h : S2448EtaleAmalgamation K) : S2448ConcreteAmalgam :=
  h baseScheme coverPresieve coverPresieve_mem

/-- The concrete amalgamation follows from the S2134 effective-descent target. -/
theorem concreteAmalgam_of_target
    (h : S2134EffDescentOnEtaleFamilies (K := K)) : S2448ConcreteAmalgam :=
  concreteAmalgam_of_etaleAmalgamation ((etaleAmalgamation_iff_S2134).mpr h)

/-- The concrete amalgamation follows from the D9 stack target. -/
theorem concreteAmalgam_of_stack
    (h : S2093LargeSheafStackMissing (K := K)) : S2448ConcreteAmalgam :=
  concreteAmalgam_of_target (S2134FirstMissing_of_stackMissing h)

/-! ## 6. The exact first missing, and base-case summary -/

/-- **The exact first missing for the concrete amalgamation.**  It is the general
slice-sheaf amalgamation (equivalently effective descent / Cech descent for the slice
topos) on the D9 site.  No inhabitant is asserted; at the concrete cover this is
exactly the construction which Mathlib v4.32.2 does not provide. -/
def S2448FirstMissing : Prop := S2448EtaleAmalgamation K

/-- The named missing implies the concrete amalgamation. -/
theorem concreteAmalgam_of_firstMissing
    (h : S2448FirstMissing) : S2448ConcreteAmalgam :=
  concreteAmalgam_of_etaleAmalgamation h

/-- The concrete cover is genuinely outside the base-case class: the generated sieve is
proper and no arrow is a split epimorphism, so neither
`hasEffectiveDescentPresieve_of_generate_top` nor
`hasEffectiveDescentPresieve_of_contains_isSplitEpi` applies to it. -/
theorem concreteCover_not_baseCase :
    Sieve.generate coverPresieve ≠ ⊤ ∧
      (∀ i : Bool, ¬ IsSplitEpi (coverArrow i)) ∧
      ¬ coverPresieve (𝟙 baseScheme) :=
  ⟨generate_coverPresieve_ne_top, coverArrow_not_isSplitEpi, id_not_mem_coverPresieve⟩

/-! ## 7. Interface checks and axiom footprint -/

#check @baseScheme
#check @coverObj
#check @coverArrow
#check @coverPresieve
#check @coverPresieve_mem
#check @generate_coverPresieve_ne_top
#check @coverArrow_not_isSplitEpi
#check @coverArrow_false_ne_true
#check @coverPresieve_ne_singleton_id
#check @S2448ConcreteAmalgam
#check @concreteAmalgam_iff_effectiveDescent
#check @S2448ConcreteAmalgamIndex
#check @concreteAmalgamIndex_iff
#check @concreteStackFor_iff_prestack_and_amalgam
#check @S2448EtaleAmalgamation
#check @etaleAmalgamation_iff_S2134
#check @concreteAmalgam_of_etaleAmalgamation
#check @concreteAmalgam_of_target
#check @concreteAmalgam_of_stack
#check @S2448FirstMissing
#check @concreteAmalgam_of_firstMissing
#check @concreteCover_not_baseCase

#print axioms coverPresieve_mem
#print axioms generate_coverPresieve_ne_top
#print axioms id_not_mem_coverPresieve
#print axioms coverArrow_not_isSplitEpi
#print axioms coverArrow_false_ne_true
#print axioms coverPresieve_ne_singleton_id
#print axioms concreteAmalgam_iff_effectiveDescent
#print axioms concreteAmalgamIndex_iff
#print axioms concreteStackFor_iff_prestack_and_amalgam
#print axioms etaleAmalgamation_iff_S2134
#print axioms concreteAmalgam_of_etaleAmalgamation
#print axioms concreteAmalgam_of_target
#print axioms concreteAmalgam_of_stack
#print axioms concreteAmalgam_of_firstMissing
#print axioms concreteCover_not_baseCase

end LeanFormal.IUT.XiFPaper.S2448GeneralCoverActual
