import tmp.sheaf.xif.paper.S1513HDDOutputBindingActual

/-!
# S1551: the actual HDD image generator family, or the precise first missing datum

## Context

S1500 records the output-dependent rank-2 HDD local lattice target
S1500OutputDependentHDDLattice I s.  S1513 showed that its binding field
imageGenerator is too weak: for every source the output-independent S1476
free lattice inhabits the target, while the genuine binding needs

  two output/place-indexed points of the actual image D.image o
  whose v-coordinates lie in O_v and are nonzero,

packaged as S1513ImageGeneratorFamily D.  The four image fields of the S1402
source say nothing about integrality, and S1513's singleton source at a
non-integral point admits no such family.  The task of this file is to try to
construct the family from the HDD theta/det data or from the actual integrality
coordinates of the S1402 image, or else to record the precise first missing
structure.

## Results

1.  [REDUCTION] The two-point family is exactly a single point per output and
    place.  S1513ImageGeneratorFamily D is inhabited if and only if for every
    output o and place v there is one point x of D.image o with x v in O_v and
    x v nonzero.  S1551IntegralImagePoint D is that single-point datum;
    Nonempty (S1551IntegralImagePoint D) is equivalent to
    Nonempty (S1513ImageGeneratorFamily D).  Given the point datum the S1500
    target with the actual image generator is constructed (conditional
    constructor s1551S1500OfPointFamily).

2.  [BUILT] The only actual local-field-valued image family on the S1402
    dependent product in the donor chain is the actual SHE 1-column reading image
    S1417HDDImageFamilyActual.outputReadingImage, the singleton of the
    unit-section point.  Its coordinates are integral (= 1) and nonzero, so
    S1513ImageGeneratorFamily is genuinely inhabited for the actual source
    s1551UnitImageSource built from it.  We prove that every generator
    family over that image is the unit reading point, and that the induced
    lattice is exactly the output-independent free lattice
    s1476LocalLattice 2 v.  This degenerate actual fill is therefore not the
    paper object; the file proves this equality instead of asserting it.  The
    actual image is provably output-independent.

3.  [PROVED] The det (x) M bookkeeping cannot be the missing input:
    replacing detData does not change the generator-family type, and the
    actual reading source and S1513's non-integral singleton source have the
    same detData yet opposite generator status.

4.  [PROVED] For a singleton image at x, the family exists if and only if
    x is integral at every place of s.  This completes S1513's
    one-directional non-integral obstruction into a criterion.

5.  [PROVED] The generator structure is not a disguised free lattice.  The
    actual uniformizer q-candidates of the completed DVRs at the rational
    places (LocalQParameter) form an actual point which is integral and
    nonzero at every place and has valuation below one.  The singleton source
    at that point admits a genuine generator family whose lattice is provably
    not the free lattice s1476LocalLattice 2 v (the vector with first
    coordinate 1 is not in it).  Hence the free-lattice collapse proved for
    the SHE reading image is a property of that actual image, not of
    S1513ImageGeneratorFamily.

6.  [MISSING] The precise first missing structure is recorded as
    S1551HDDPaperImageGenerator: an actual output-dependent HDD source
    (S1417's missing first field) together with one integral nonzero image
    point per output and place, with output dependence of the image recorded as
    a necessary condition.  No inhabitant is asserted, and the actual SHE
    reading image provably cannot satisfy the output-dependence condition.

No sorry, axiom, True/PUnit surrogate, rank-one surrogate or free lattice is
used as the paper object.  The output-independent free lattice appears only as
the proved value of the degenerate actual image, i.e. as the exact statement
that the available actual image fill is output-independent.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1551HDDImageGeneratorActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1476HDDRankActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1417HDDImageFamilyActual
open LeanFormal.IUT.XiFPaper.S1500HDDOutputDependentActual
open LeanFormal.IUT.XiFPaper.S1513HDDOutputBindingActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}
variable {s : Finset (NumberField.FinitePlace ℚ)}

/-! ## 1. The missing datum in single-point form -/

/-- One integral nonzero image point at a fixed output and place: the exact
content of one of the two S1513 generator slots at that place. -/
def s1551IntegralImagePoint (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) : Prop :=
  ∃ x ∈ D.image o, x v ∈ (CompletionIntegers v.1 : Set (Completion v.1)) ∧ x v ≠ 0

theorem s1551IntegralImagePoint_of_generator {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D) (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    s1551IntegralImagePoint D o v :=
  ⟨G.gen o v 0, G.mem o v 0, G.integral o v 0, G.nonzero o v 0⟩

/-- A single integral nonzero image point per output and place yields the S1513
generator family: use the same point in both slots.  The two-point family is
therefore not more data than one point. -/
noncomputable def s1551GeneratorFamilyOfPoints {D : S1402DependentHDDSource I s}
    (h : ∀ (o : Theorem311Output I)
      (v : {v : NumberField.FinitePlace ℚ // v ∈ s}), s1551IntegralImagePoint D o v) :
    S1513ImageGeneratorFamily D where
  gen o v _ := Classical.choose (h o v)
  mem o v _ := (Classical.choose_spec (h o v)).1
  integral o v _ := (Classical.choose_spec (h o v)).2.1
  nonzero o v _ := (Classical.choose_spec (h o v)).2.2

/-- [REDUCTION] The S1513 two-point generator family is inhabited exactly when
one integral nonzero image point exists at every output and place. -/
theorem s1551Nonempty_generatorFamily_iff {D : S1402DependentHDDSource I s} :
    Nonempty (S1513ImageGeneratorFamily D) ↔
      ∀ (o : Theorem311Output I)
        (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
        s1551IntegralImagePoint D o v :=
  ⟨fun ⟨G⟩ o v => s1551IntegralImagePoint_of_generator G o v,
   fun h => ⟨s1551GeneratorFamilyOfPoints h⟩⟩

/-- The precise first missing structure in its minimal form: one actual image
point per output and place whose value at that place is integral and nonzero.
No inhabitant is asserted. -/
structure S1551IntegralImagePoint (D : S1402DependentHDDSource I s) where
  point : (o : Theorem311Output I) → (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) →
    S1513DependentPoint s
  mem : ∀ (o : Theorem311Output I) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    point o v ∈ D.image o
  integral : ∀ (o : Theorem311Output I) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    point o v v ∈ (CompletionIntegers v.1 : Set (Completion v.1))
  nonzero : ∀ (o : Theorem311Output I) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    point o v v ≠ 0

namespace S1551IntegralImagePoint

variable {D : S1402DependentHDDSource I s}

/-- The single-point datum produces the S1513 generator family. -/
def toGeneratorFamily (P : S1551IntegralImagePoint D) : S1513ImageGeneratorFamily D where
  gen o v _ := P.point o v
  mem o v _ := P.mem o v
  integral o v _ := P.integral o v
  nonzero o v _ := P.nonzero o v

/-- The S1513 generator family produces the single-point datum, taking the
first slot. -/
def ofGeneratorFamily (G : S1513ImageGeneratorFamily D) : S1551IntegralImagePoint D where
  point o v := G.gen o v 0
  mem o v := G.mem o v 0
  integral o v := G.integral o v 0
  nonzero o v := G.nonzero o v 0

theorem ofGenerator_toGenerator (P : S1551IntegralImagePoint D) :
    ofGeneratorFamily (toGeneratorFamily P) = P := by
  cases P
  rfl

theorem nonempty_iff :
    Nonempty (S1551IntegralImagePoint D) ↔ Nonempty (S1513ImageGeneratorFamily D) :=
  ⟨fun ⟨P⟩ => ⟨toGeneratorFamily P⟩, fun ⟨G⟩ => ⟨ofGeneratorFamily G⟩⟩

/-- Each generated coordinate vector is the actual image point placed in its
coordinate. -/
theorem generatorVector_toGeneratorFamily (P : S1551IntegralImagePoint D)
    (o : Theorem311Output I) (v : {v : NumberField.FinitePlace ℚ // v ∈ s})
    (i : Fin 2) :
    s1513GeneratorVector P.toGeneratorFamily o v i = Pi.single i (P.point o v v) := rfl

end S1551IntegralImagePoint

/-! ## 2. The conditional S1500 binding from the single-point datum -/

/-- The actual binding record built from a source and the single-point integral
image datum. -/
noncomputable def s1551BindingOfPointFamily (D : S1402DependentHDDSource I s)
    (P : S1551IntegralImagePoint D) : S1513HDDOutputBinding I s where
  source := D
  generator := P.toGeneratorFamily

@[simp] theorem s1551BindingOfPointFamily_source (D : S1402DependentHDDSource I s)
    (P : S1551IntegralImagePoint D) :
    (s1551BindingOfPointFamily D P).source = D := rfl

@[simp] theorem s1551BindingOfPointFamily_lattice (D : S1402DependentHDDSource I s)
    (P : S1551IntegralImagePoint D) (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    (s1551BindingOfPointFamily D P).lattice o v =
      s1513DiagonalLattice P.toGeneratorFamily o v := rfl

/-- The S1500 target with the actual image generator, built from the
single-point datum. -/
noncomputable def s1551S1500OfPointFamily (D : S1402DependentHDDSource I s)
    (P : S1551IntegralImagePoint D) : S1500OutputDependentHDDLattice I s :=
  (s1551BindingOfPointFamily D P).toS1500

/-- The S1500 image generator of the constructed binding is exactly the actual
image point of the datum. -/
@[simp] theorem s1551S1500OfPointFamily_imageGenerator
    (D : S1402DependentHDDSource I s) (P : S1551IntegralImagePoint D)
    (o : Theorem311Output I) (v : {v : NumberField.FinitePlace ℚ // v ∈ s})
    (i : Fin 2) :
    (s1551S1500OfPointFamily D P).imageGenerator o v i = P.point o v := rfl

/-- [CONDITIONAL] Given the missing single-point datum, the S1500 target is
inhabited with a generator family taken from the actual image. -/
theorem s1551S1500OfPointFamily_lattice_eq_diagonal
    (D : S1402DependentHDDSource I s) (P : S1551IntegralImagePoint D)
    (o : Theorem311Output I) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    (s1551S1500OfPointFamily D P).lattice o v =
      s1513DiagonalLattice P.toGeneratorFamily o v := rfl

/-! ## 3. The actual SHE reading image: the only actual fill, and its exact value -/

/-- The actual S1402 source whose image is the actual SHE 1-column reading
image: the singleton of the unit-section point.  The det (x) M bookkeeping is
an explicit input, as in S1513/S1417. -/
noncomputable def s1551UnitImageSource
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    S1402DependentHDDSource I s where
  image := outputReadingImage I s
  compact_closure := outputReadingImage_compact I s
  nonempty := outputReadingImage_nonempty I s
  coordinate_nonzero := outputReadingImage_coordinate_nonzero I s
  detData := det

/-- Every coordinate of the actual reading point is the integral unit. -/
theorem s1551UnitPoint_integral (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    outputReadingPoint I s o v ∈ (CompletionIntegers v.1 : Set (Completion v.1)) := by
  rw [outputReadingPoint_eq_one]
  exact one_mem _

/-- The actual reading point is nonzero at every place. -/
theorem s1551UnitPoint_ne_zero (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    outputReadingPoint I s o v ≠ 0 :=
  outputReadingPoint_ne_zero I s o v

/-- [BUILT] The actual integral image generator family of the actual SHE
reading image.  Both slots are the actual reading point, which is integral
(= 1) and nonzero at every place. -/
noncomputable def s1551UnitGeneratorFamily
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    S1513ImageGeneratorFamily (s1551UnitImageSource (I := I) det) where
  gen o v _ := outputReadingPoint I s o
  mem o v i := by
    show outputReadingPoint I s o ∈ ({outputReadingPoint I s o} :
      Set ((v : {v : NumberField.FinitePlace ℚ // v ∈ s}) → S1402DependentE s v))
    exact rfl
  integral o v i := s1551UnitPoint_integral (I := I) o v
  nonzero o v i := s1551UnitPoint_ne_zero (I := I) o v

/-- The actual binding record of the SHE reading image. -/
noncomputable def s1551UnitBinding
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    S1513HDDOutputBinding I s where
  source := s1551UnitImageSource (I := I) det
  generator := s1551UnitGeneratorFamily (I := I) det

/-- The actual reading image does not depend on the output: it is the constant
singleton of the unit point. -/
theorem s1551UnitImage_output_independent
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (o o' : Theorem311Output I) :
    (s1551UnitImageSource (I := I) det).image o =
      (s1551UnitImageSource (I := I) det).image o' :=
  outputReadingImage_output_independent I s o o'

/-- Every generator family over the actual reading image is the unit reading
point: the image is a singleton. -/
theorem s1551UnitImage_gen_eq
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (G : S1513ImageGeneratorFamily (s1551UnitImageSource (I := I) det))
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    G.gen o v i = outputReadingPoint I s o := by
  have h := G.mem o v i
  simpa [s1551UnitImageSource, outputReadingImage] using h

/-- The local generator of the actual fill is the integral unit. -/
theorem s1551UnitLocalGenerator_eq_one
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    s1513LocalGenerator (s1551UnitGeneratorFamily (I := I) det) o v i = 1 := by
  rw [Subtype.ext_iff]
  rw [s1513LocalGenerator_coe]
  rfl

/-- If the two local generators are the integral unit, the diagonal map is
exactly the free integral localization map of S1476. -/
theorem s1551DiagonalMap_eq_free_of_gen_unit
    {D : S1402DependentHDDSource I s} (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s})
    (hgen : ∀ i, G.gen o v i v = 1) :
    s1513DiagonalMap G o v = s1476IntegralMap 2 v.1 := by
  apply LinearMap.ext
  intro a
  funext i
  rw [s1513DiagonalMap_apply, s1476IntegralMap_apply]
  have hloc : s1513LocalGenerator G o v i = 1 := by
    rw [Subtype.ext_iff]
    rw [s1513LocalGenerator_coe, hgen i]
    rfl
  show ((s1513LocalGenerator G o v i * a i : CompletionIntegers v.1) : Completion v.1) =
    ((a i : CompletionIntegers v.1) : Completion v.1)
  rw [hloc, one_mul]

/-- [PROVED] The lattice induced by the actual fill is exactly the
output-independent free rank-2 lattice O_v^2 = s1476LocalLattice 2 v.  This
is the precise sense in which the only actual image available gives the S1476
free lattice rather than the paper object. -/
theorem s1551UnitLattice_eq_free
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    (s1551UnitBinding (I := I) det).lattice o v = s1476LocalLattice 2 v.1 := by
  show s1513DiagonalLattice (s1551UnitGeneratorFamily (I := I) det) o v =
    s1476LocalLattice 2 v.1
  unfold s1513DiagonalLattice s1476LocalLattice
  rw [s1551DiagonalMap_eq_free_of_gen_unit (s1551UnitGeneratorFamily (I := I) det) o v
    (fun i => rfl)]

/-- [PROVED] The actual fill is output-independent, exactly like the S1476
free lattice. -/
theorem s1551UnitLattice_output_independent
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (o o' : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    (s1551UnitBinding (I := I) det).lattice o v =
      (s1551UnitBinding (I := I) det).lattice o' v := by
  rw [s1551UnitLattice_eq_free, s1551UnitLattice_eq_free]

/-- [PROVED] Every generator family over the actual reading image induces
exactly the free lattice, not just the canonical one.  Hence no choice of
generator over the available actual image can produce the paper object. -/
theorem s1551UnitLattice_any_eq_free
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (G : S1513ImageGeneratorFamily (s1551UnitImageSource (I := I) det))
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    s1513DiagonalLattice G o v = s1476LocalLattice 2 v.1 := by
  unfold s1513DiagonalLattice s1476LocalLattice
  rw [s1551DiagonalMap_eq_free_of_gen_unit G o v
    (fun i => by
      rw [s1551UnitImage_gen_eq (I := I) det G o v i, outputReadingPoint_eq_one])]

/-- The S1500 target built from the actual reading image has the free lattice
at every output and place. -/
theorem s1551UnitS1500Lattice_eq_free
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    ((s1551UnitBinding (I := I) det).toS1500).lattice o v =
      s1476LocalLattice 2 v.1 :=
  s1551UnitLattice_eq_free (I := I) det o v

/-- The actual reading image carries no output dependence. -/
theorem s1551UnitImage_not_output_dependent
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    ¬ ∃ (o o' : Theorem311Output I),
      (s1551UnitImageSource (I := I) det).image o ≠
        (s1551UnitImageSource (I := I) det).image o' := by
  rintro ⟨o, o', hne⟩
  exact hne (s1551UnitImage_output_independent (I := I) det o o')

/-! ## 4. The det bookkeeping cannot be the missing input -/

/-- Replace the det (x) M bookkeeping of a source, keeping its actual image. -/
noncomputable def s1551ReplaceDet (D : S1402DependentHDDSource I s)
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    S1402DependentHDDSource I s :=
  { D with detData := det }

@[simp] theorem s1551ReplaceDet_image (D : S1402DependentHDDSource I s)
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    (s1551ReplaceDet D det).image = D.image := rfl

/-- [PROVED] Replacing the det bookkeeping does not change the generator-family
type: the missing datum depends only on the actual image. -/
theorem s1551Nonempty_generatorFamily_replaceDet
    (D : S1402DependentHDDSource I s)
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    Nonempty (S1513ImageGeneratorFamily (s1551ReplaceDet D det)) ↔
      Nonempty (S1513ImageGeneratorFamily D) := by
  rw [s1551Nonempty_generatorFamily_iff, s1551Nonempty_generatorFamily_iff]
  constructor
  · intro h o v
    have h' := h o v
    simp only [s1551IntegralImagePoint, s1551ReplaceDet_image] at h' ⊢
    exact h'
  · intro h o v
    have h' := h o v
    simp only [s1551IntegralImagePoint, s1551ReplaceDet_image] at h' ⊢
    exact h'

/-- [PROVED] The actual reading source and S1513's non-integral singleton
source have the same det bookkeeping yet opposite generator status.  Hence the
det data are not sufficient for the missing datum. -/
theorem s1551SameDetData_oppositeStatus
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (x : S1513DependentPoint s) (hx : ∀ v, x v ≠ 0)
    (v0 : {v : NumberField.FinitePlace ℚ // v ∈ s})
    (hv0 : x v0 ∉ (CompletionIntegers v0.1 : Set (Completion v0.1))) :
    (s1551UnitImageSource (I := I) det).detData =
        (s1513SingletonSource (I := I) x hx det).detData ∧
      Nonempty (S1513ImageGeneratorFamily (s1551UnitImageSource (I := I) det)) ∧
      ¬ Nonempty (S1513ImageGeneratorFamily
        (s1513SingletonSource (I := I) x hx det)) :=
  ⟨rfl, ⟨s1551UnitGeneratorFamily (I := I) det⟩,
   s1513SingletonSource_no_generator (I := I) x hx det v0 hv0⟩

/-! ## 5. The singleton integrality criterion -/

/-- [PROVED] For an image that is the singleton x with x nonzero at every
place, the S1513 generator family exists if and only if every coordinate of
x is integral.  This completes S1513's non-integral obstruction. -/
theorem s1551Singleton_generatorFamily_iff
    (x : S1513DependentPoint s) (hx : ∀ v, x v ≠ 0)
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    Nonempty (S1513ImageGeneratorFamily (s1513SingletonSource (I := I) x hx det)) ↔
      ∀ v, x v ∈ (CompletionIntegers v.1 : Set (Completion v.1)) := by
  constructor
  · intro h v
    obtain ⟨G⟩ := h
    let o : Theorem311Output I := theorem311Output I
    have hmem : G.gen o v 0 ∈ (s1513SingletonSource (I := I) x hx det).image o :=
      G.mem o v 0
    have hgen : G.gen o v 0 = x := by
      simpa [s1513SingletonSource] using hmem
    have hint := G.integral o v 0
    rwa [hgen] at hint
  · intro h
    exact ⟨{ gen := fun _ _ _ => x
             mem := fun o v i => by
               show x ∈ ({x} : Set (S1513DependentPoint s))
               exact rfl
             integral := fun o v i => h v
             nonzero := fun o v i => hx v }⟩

/-! ## 6. The generator structure is not a disguised free lattice -/

/-- The actual q-candidate of the completed DVR at a rational finite place
(LocalQParameter): nonzero with valuation below one. -/
noncomputable def s1551UniformizerCandidate
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    FinitePlaceQCandidate v.1 :=
  Classical.choice (finitePlaceQCandidate_nonempty v.1)

/-- The actual uniformizer point: at each place the q-candidate of the
completed DVR.  Its coordinates are integral and nonzero at every place.  This
is actual local data, not the paper HDD theta/det image. -/
noncomputable def s1551UniformizerPoint
    (s : Finset (NumberField.FinitePlace ℚ)) : S1513DependentPoint s :=
  fun v => (s1551UniformizerCandidate v).q

theorem s1551UniformizerPoint_ne_zero
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    s1551UniformizerPoint s v ≠ 0 :=
  (s1551UniformizerCandidate v).q_ne_zero

theorem s1551UniformizerPoint_integral
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    s1551UniformizerPoint s v ∈
      (CompletionIntegers v.1 : Set (Completion v.1)) := by
  show Valued.v (s1551UniformizerPoint s v) ≤ 1
  exact le_of_lt (s1551UniformizerCandidate v).valuation_lt_one

/-- The value of the S1513 diagonal map, read through the actual image
generator. -/
theorem s1551DiagonalMap_apply_value {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D) (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s})
    (a : Fin 2 → CompletionIntegers v.1) (i : Fin 2) :
    s1513DiagonalMap G o v a i =
      (G.gen o v i v : Completion v.1) * (a i : Completion v.1) := by
  rw [s1513DiagonalMap_apply]
  rfl

/-- A uniformizer coordinate cannot satisfy q * a = 1 with a integral: that
would put the inverse of the uniformizer in O_v, contradicting valuation below
one. -/
theorem s1551Uniformizer_not_mul_eq_one
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s})
    (a : CompletionIntegers v.1) :
    (s1551UniformizerPoint s v : Completion v.1) * (a : Completion v.1) ≠ 1 := by
  intro ha
  have hq0 := s1551UniformizerPoint_ne_zero (s := s) v
  have hqlt := (s1551UniformizerCandidate v).valuation_lt_one
  have hqmem := s1551UniformizerPoint_integral (s := s) v
  have hqval_ne : Valued.v (s1551UniformizerPoint s v) ≠ 0 := by
    intro h
    exact hq0 (((Valued.v :
      Valuation (Completion v.1) (WithZero (Multiplicative Int))).map_eq_zero_iff).mp h)
  have hqpos : 0 < Valued.v (s1551UniformizerPoint s v) :=
    lt_of_le_of_ne (zero_le) (Ne.symm hqval_ne)
  have hqone_lt : 1 < (Valued.v (s1551UniformizerPoint s v))⁻¹ :=
    one_lt_inv_iff₀.mpr ⟨hqpos, hqlt⟩
  have ha_eq : (a : Completion v.1) =
      (s1551UniformizerPoint s v : Completion v.1)⁻¹ := by
    calc (a : Completion v.1) = 1 * (a : Completion v.1) := (one_mul _).symm
      _ = ((s1551UniformizerPoint s v : Completion v.1)⁻¹ *
            (s1551UniformizerPoint s v : Completion v.1)) * (a : Completion v.1) := by
          rw [inv_mul_cancel₀ hq0]
      _ = (s1551UniformizerPoint s v : Completion v.1)⁻¹ *
            ((s1551UniformizerPoint s v : Completion v.1) * (a : Completion v.1)) := by
          rw [mul_assoc]
      _ = (s1551UniformizerPoint s v : Completion v.1)⁻¹ * 1 := by rw [ha]
      _ = (s1551UniformizerPoint s v : Completion v.1)⁻¹ := mul_one _
  have hinvmem : (s1551UniformizerPoint s v : Completion v.1)⁻¹ ∈
      (CompletionIntegers v.1 : Set (Completion v.1)) := by
    rw [← ha_eq]
    exact a.2
  have hle : Valued.v ((s1551UniformizerPoint s v : Completion v.1)⁻¹) ≤ 1 :=
    hinvmem
  rw [map_inv₀] at hle
  exact not_le_of_gt hqone_lt hle

/-- The actual singleton source at the uniformizer point. -/
noncomputable def s1551UniformizerSource
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    S1402DependentHDDSource I s :=
  s1513SingletonSource (s1551UniformizerPoint s)
    (s1551UniformizerPoint_ne_zero (s := s)) det

/-- [BUILT] The generator family of the uniformizer source: both slots are the
actual uniformizer point. -/
noncomputable def s1551UniformizerGeneratorFamily
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    S1513ImageGeneratorFamily (s1551UniformizerSource (I := I) det) where
  gen _ _ _ := s1551UniformizerPoint s
  mem o v i := by
    show s1551UniformizerPoint s ∈
      ({s1551UniformizerPoint s} : Set (S1513DependentPoint s))
    exact rfl
  integral o v i := s1551UniformizerPoint_integral (s := s) v
  nonzero o v i := s1551UniformizerPoint_ne_zero (s := s) v

/-- Membership in the uniformizer diagonal lattice: exactly the vectors of the
form q * a with a integral. -/
theorem s1551UniformizerLattice_mem_iff
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (o : Theorem311Output I) (v : {v : NumberField.FinitePlace ℚ // v ∈ s})
    (x : Fin 2 → Completion v.1) :
    x ∈ s1513DiagonalLattice (s1551UniformizerGeneratorFamily (I := I) det) o v ↔
      ∃ a : Fin 2 → CompletionIntegers v.1,
        ∀ i, x i = (s1551UniformizerPoint s v : Completion v.1) *
          (a i : Completion v.1) := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, fun i => ?_⟩
    rw [s1551DiagonalMap_apply_value]
    simp only [s1551UniformizerGeneratorFamily]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    funext i
    rw [s1551DiagonalMap_apply_value]
    simp only [s1551UniformizerGeneratorFamily]
    rw [← ha i]

/-- [PROVED] The generator structure is not a disguised free lattice: the
uniformizer diagonal lattice is not the free lattice s1476LocalLattice 2 v.
The vector with first coordinate 1 is not in it. -/
theorem s1551UniformizerLattice_ne_free
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (o : Theorem311Output I) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    s1513DiagonalLattice (s1551UniformizerGeneratorFamily (I := I) det) o v ≠
      s1476LocalLattice 2 v.1 := by
  intro hEq
  have hmemFree : (Pi.single 0 (1 : Completion v.1) : Fin 2 → Completion v.1) ∈
      s1476LocalLattice 2 v.1 := by
    refine ⟨Pi.single 0 (1 : CompletionIntegers v.1), ?_⟩
    funext i
    rw [s1476IntegralMap_apply]
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi]
      simp
  rw [← hEq] at hmemFree
  obtain ⟨a, ha⟩ :=
    (s1551UniformizerLattice_mem_iff (s := s) (I := I) det o v _).mp hmemFree
  have h0 := ha 0
  rw [Pi.single_eq_same] at h0
  exact s1551Uniformizer_not_mul_eq_one (s := s) v (a 0) h0.symm

/-! ## 7. The precise first missing structure at paper level -/

/-- [MISSING] The paper-level first missing structure, as two independent
inputs: an actual output-dependent HDD source (S1417's missing image family;
no inhabitant exists in the donor chain) together with one integral nonzero
image point at every output and place (S1513's missing binding, in the
single-point form proved equivalent above).  The output dependence of the image
is recorded as a necessary condition; it is not by itself a construction of the
paper's theta/det image.

No inhabitant is asserted. -/
structure S1551HDDPaperImageGenerator where
  source : S1402DependentHDDSource I s
  generator : S1551IntegralImagePoint source
  image_output_dependent :
    ∃ (o o' : Theorem311Output I), source.image o ≠ source.image o'

/-- [PROVED] The actual reading image cannot be the source of the paper-level
missing structure: its image is output-independent. -/
theorem s1551PaperImageGenerator_not_unitImage
    (P : S1551HDDPaperImageGenerator (I := I) (s := s))
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (h : P.source.image = (s1551UnitImageSource (I := I) det).image) : False := by
  obtain ⟨o, o', hne⟩ := P.image_output_dependent
  refine hne ?_
  rw [h]
  exact s1551UnitImage_output_independent (I := I) det o o'

/-- [PROVED] The actual reading source supplies the generator family and the
S1500 target, but its lattice is the output-independent free lattice; hence it
does not fill the paper-level missing structure. -/
theorem s1551UnitImage_not_paper
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    (∃ (G : S1513ImageGeneratorFamily (s1551UnitImageSource (I := I) det)),
        ∀ (o : Theorem311Output I)
          (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
          s1513DiagonalLattice G o v = s1476LocalLattice 2 v.1) ∧
      ¬ ∃ (o o' : Theorem311Output I),
          (s1551UnitImageSource (I := I) det).image o ≠
            (s1551UnitImageSource (I := I) det).image o' :=
  ⟨⟨s1551UnitGeneratorFamily (I := I) det,
    fun o v => s1551UnitLattice_any_eq_free (I := I) det
      (s1551UnitGeneratorFamily (I := I) det) o v⟩,
   s1551UnitImage_not_output_dependent (I := I) det⟩

/-! ## 8. Checks and axiom audit -/

#check s1551IntegralImagePoint
#check s1551Nonempty_generatorFamily_iff
#check S1551IntegralImagePoint
#check S1551IntegralImagePoint.nonempty_iff
#check s1551BindingOfPointFamily
#check s1551S1500OfPointFamily
#check s1551UnitImageSource
#check s1551UnitGeneratorFamily
#check s1551UnitBinding
#check s1551UnitLattice_eq_free
#check s1551UnitLattice_output_independent
#check s1551UnitLattice_any_eq_free
#check s1551UnitS1500Lattice_eq_free
#check s1551UnitImage_output_independent
#check s1551UnitImage_not_output_dependent
#check s1551ReplaceDet
#check s1551Nonempty_generatorFamily_replaceDet
#check s1551SameDetData_oppositeStatus
#check s1551Singleton_generatorFamily_iff
#check S1551HDDPaperImageGenerator
#check s1551PaperImageGenerator_not_unitImage
#check s1551UnitImage_not_paper
#check s1551UniformizerPoint
#check s1551UniformizerPoint_integral
#check s1551DiagonalMap_apply_value
#check s1551Uniformizer_not_mul_eq_one
#check s1551UniformizerSource
#check s1551UniformizerGeneratorFamily
#check s1551UniformizerLattice_mem_iff
#check s1551UniformizerLattice_ne_free

#print axioms s1551UniformizerLattice_ne_free
#print axioms s1551Uniformizer_not_mul_eq_one
#print axioms s1551Nonempty_generatorFamily_iff
#print axioms S1551IntegralImagePoint.nonempty_iff
#print axioms s1551UnitLattice_eq_free
#print axioms s1551UnitLattice_any_eq_free
#print axioms s1551Nonempty_generatorFamily_replaceDet
#print axioms s1551SameDetData_oppositeStatus
#print axioms s1551Singleton_generatorFamily_iff
#print axioms s1551PaperImageGenerator_not_unitImage
#print axioms s1551UnitImage_not_paper

end LeanFormal.IUT.XiFPaper.S1551HDDImageGeneratorActual
