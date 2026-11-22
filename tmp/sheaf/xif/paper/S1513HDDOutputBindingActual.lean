import tmp.sheaf.xif.paper.S1500HDDOutputDependentActual
import tmp.sheaf.xif.paper.S1476HDDRankActual
import tmp.sheaf.xif.paper.S1402HDDDependentSourceActual
import tmp.sheaf.xif.paper.S1417HDDImageFamilyActual

/-!
# S1513: actual binding of an output-dependent rank-2 O_v-lattice family
to the S1402 image, or the precise first missing binding

S1500 recorded the target structure
S1500OutputDependentHDDLattice I s with the binding field

  imageGenerator     : output -> place -> Fin 2 -> (place -> localField)
  imageGenerator_mem : imageGenerator o v i in source.image o

but supplied no inhabitant.  S1476 supplies an actual free rank-2 integral
local lattice s1476LocalLattice 2 v, but that lattice is independent of the
Theorem311Output argument and therefore cannot itself be the HDD
output-dependent lattice.  S1402/S1417 record the output-dependent image
family source.image as a set of product-local-field points.

This file does two things.

1.  It constructs the output-dependent rank-2 O_v-lattice family from an
    actual image generator family.  The generator family consists of two
    product points of source.image per output and place whose coordinates
    in the chosen place are integral and nonzero.  The local lattice is the
    diagonal O_v-span of those two values.  It is free, finite, integral,
    of rank two and full in K_v^2, and its definition uses the actual image
    values, not a constant free bundle.  Consequently an inhabitant of the
    S1500 target is obtained from such a generator family.  The source and
    the generator family are explicit inputs; neither is constructed in this
    file, and no unconditional inhabitant of the S1500 target is asserted.

2.  It isolates the precise first missing binding.  The S1402 image is
    scalar-valued per place.  The fields of S1402DependentHDDSource say
    nothing about integrality of the image coordinates, and nothing that
    forces two distinct image points to be usable as a rank-two local basis.
    The missing datum is S1513ImageGeneratorFamily: two output/place-indexed
    points of the actual image with integral, nonzero coordinates.  We prove
    that the S1500 target alone does not force actual binding: for every
    source it is inhabited by the output-independent S1476 lattice.  We also
    prove that a source whose image is a singleton at a point with a
    non-integral coordinate does not admit the missing generator family.

No sorry, axiom, True, Nonempty surrogate or rank-one replacement is used.
The output-independent lattice appears only in a documented
under-specification witness proving that the S1500 binding field alone is
insufficient; it is not presented as the paper object.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1513HDDOutputBindingActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1476HDDRankActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1417HDDImageFamilyActual
open LeanFormal.IUT.XiFPaper.S1500HDDOutputDependentActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}
variable {s : Finset (NumberField.FinitePlace ℚ)}

/-- The actual dependent product of local fields over the finite set s. -/
abbrev S1513DependentPoint (s : Finset (NumberField.FinitePlace ℚ)) : Type :=
  (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) → S1402DependentE s v

/-! ## 1. The precise missing input: an integral image generator family -/

/-- The precise first missing binding: two output/place-indexed points of the
actual S1402 image whose values at the selected place are integral elements of
O_v and are nonzero.  These are the two diagonal coordinates of the local
rank-two lattice at that place.  No inhabitant is asserted. -/
structure S1513ImageGeneratorFamily
    (D : S1402DependentHDDSource I s) where
  gen : (o : Theorem311Output I) → (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) →
    Fin 2 → S1513DependentPoint s
  mem : ∀ (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2),
    gen o v i ∈ D.image o
  integral : ∀ (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2),
    gen o v i v ∈ (CompletionIntegers v.1 : Set (Completion v.1))
  nonzero : ∀ (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2),
    gen o v i v ≠ 0

/-- The integral generator value as an element of O_v. -/
noncomputable def s1513LocalGenerator {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    CompletionIntegers v.1 :=
  ⟨G.gen o v i v, G.integral o v i⟩

@[simp] theorem s1513LocalGenerator_coe {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    (s1513LocalGenerator G o v i : Completion v.1) = G.gen o v i v := rfl

theorem s1513LocalGenerator_ne_zero {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    s1513LocalGenerator G o v i ≠ 0 := by
  intro h
  apply G.nonzero o v i
  rw [← s1513LocalGenerator_coe G o v i, h]
  rfl

/-- The i-th local generator vector: the image value placed in the i-th
coordinate. -/
noncomputable def s1513GeneratorVector {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    Fin 2 → Completion v.1 :=
  Pi.single i (G.gen o v i v)

/-! ## 2. The diagonal rank-two integral lattice -/

/-- Coordinatewise multiplication by the i-th integral generator. -/
noncomputable def s1513CoordinateMap {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    (Fin 2 → CompletionIntegers v.1) →ₗ[CompletionIntegers v.1]
      CompletionIntegers v.1 where
  toFun a := s1513LocalGenerator G o v i * a i
  map_add' x y := by simp [mul_add]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf

/-- The diagonal map O_v^2 -> K_v^2 whose two columns are the integral
image generators. -/
noncomputable def s1513DiagonalMap {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    (Fin 2 → CompletionIntegers v.1) →ₗ[CompletionIntegers v.1]
      (Fin 2 → Completion v.1) :=
  LinearMap.pi (fun i =>
    (Algebra.linearMap (CompletionIntegers v.1) (Completion v.1)).comp
      (s1513CoordinateMap G o v i))

@[simp] theorem s1513DiagonalMap_apply {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s})
    (a : Fin 2 → CompletionIntegers v.1) (i : Fin 2) :
    s1513DiagonalMap G o v a i =
      algebraMap (CompletionIntegers v.1) (Completion v.1)
        (s1513LocalGenerator G o v i * a i) := rfl

theorem s1513DiagonalMap_injective {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    Function.Injective (s1513DiagonalMap G o v) := by
  intro a b hab
  funext i
  have hK :
      (s1513LocalGenerator G o v i : Completion v.1) * (a i : Completion v.1) =
        (s1513LocalGenerator G o v i : Completion v.1) * (b i : Completion v.1) := by
    have h := congrFun hab i
    rw [s1513DiagonalMap_apply, s1513DiagonalMap_apply] at h
    change (s1513LocalGenerator G o v i : Completion v.1) * (a i : Completion v.1) =
      (s1513LocalGenerator G o v i : Completion v.1) * (b i : Completion v.1) at h
    exact h
  have h : (a i : Completion v.1) = (b i : Completion v.1) :=
    mul_left_cancel₀ (G.nonzero o v i) hK
  exact Subtype.ext h

/-- The output-dependent rank-two local lattice: the image of O_v^2 under
the diagonal map determined by the actual image generators. -/
noncomputable def s1513DiagonalLattice {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    Submodule (CompletionIntegers v.1) (Fin 2 → Completion v.1) :=
  LinearMap.range (s1513DiagonalMap G o v)

noncomputable def s1513DiagonalEquiv {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    (Fin 2 → CompletionIntegers v.1) ≃ₗ[CompletionIntegers v.1]
      s1513DiagonalLattice G o v :=
  LinearEquiv.ofInjective (s1513DiagonalMap G o v) (s1513DiagonalMap_injective G o v)

instance s1513DiagonalLatticeFree {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    Module.Free (CompletionIntegers v.1) (s1513DiagonalLattice G o v) :=
  Module.Free.of_equiv (s1513DiagonalEquiv G o v)

instance s1513DiagonalLatticeFinite {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    Module.Finite (CompletionIntegers v.1) (s1513DiagonalLattice G o v) :=
  Module.Finite.equiv (s1513DiagonalEquiv G o v)

theorem s1513DiagonalLattice_finrank {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    Module.finrank (CompletionIntegers v.1) (s1513DiagonalLattice G o v) = 2 := by
  rw [← (s1513DiagonalEquiv G o v).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem s1513DiagonalLattice_integral {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s})
    {x : Fin 2 → Completion v.1} (hx : x ∈ s1513DiagonalLattice G o v) :
    ∀ i, x i ∈ (CompletionIntegers v.1 : Set (Completion v.1)) := by
  rcases hx with ⟨a, rfl⟩
  intro i
  exact (s1513LocalGenerator G o v i * a i).2

theorem s1513GeneratorVector_mem {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    s1513GeneratorVector G o v i ∈ s1513DiagonalLattice G o v := by
  refine ⟨Pi.single i (1 : CompletionIntegers v.1), ?_⟩
  funext j
  by_cases h : j = i
  · subst h
    simp [s1513GeneratorVector]
  · rw [s1513DiagonalMap_apply, Pi.single_eq_of_ne' (Ne.symm h),
      s1513GeneratorVector, Pi.single_eq_of_ne' (Ne.symm h)]
    simp

theorem s1513DiagonalLattice_eq_span {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    s1513DiagonalLattice G o v =
      Submodule.span (CompletionIntegers v.1)
        ({s1513GeneratorVector G o v 0, s1513GeneratorVector G o v 1} :
          Set (Fin 2 → Completion v.1)) := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨a, rfl⟩
    have h :
        s1513DiagonalMap G o v a =
          a 0 • s1513GeneratorVector G o v 0 +
            a 1 • s1513GeneratorVector G o v 1 := by
      funext j
      fin_cases j <;>
        simp [s1513DiagonalMap_apply, s1513GeneratorVector, Pi.single_eq_same,
          Pi.single_eq_of_ne, mul_comm, Algebra.smul_def]
    rw [h]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact s1513GeneratorVector_mem G o v 0
    · exact s1513GeneratorVector_mem G o v 1

theorem s1513Single_mem_span {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    (Pi.single i (1 : Completion v.1) : Fin 2 → Completion v.1) ∈
      Submodule.span (Completion v.1)
        (s1513DiagonalLattice G o v : Set (Fin 2 → Completion v.1)) := by
  have hmem :
      (G.gen o v i v)⁻¹ • s1513GeneratorVector G o v i ∈
        Submodule.span (Completion v.1)
          (s1513DiagonalLattice G o v : Set (Fin 2 → Completion v.1)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (s1513GeneratorVector_mem G o v i))
  have hfun :
      (G.gen o v i v)⁻¹ • s1513GeneratorVector G o v i =
        (Pi.single i (1 : Completion v.1) : Fin 2 → Completion v.1) := by
    funext j
    by_cases h : j = i
    · subst j
      simp [s1513GeneratorVector, inv_mul_cancel₀ (G.nonzero o v i)]
    · rw [Pi.smul_apply, s1513GeneratorVector,
        Pi.single_eq_of_ne' (Ne.symm h), Pi.single_eq_of_ne' (Ne.symm h)]
      simp
  rwa [hfun] at hmem

theorem s1513DiagonalLattice_span_eq_top {D : S1402DependentHDDSource I s}
    (G : S1513ImageGeneratorFamily D)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    Submodule.span (Completion v.1)
      (s1513DiagonalLattice G o v : Set (Fin 2 → Completion v.1)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← (Pi.basisFun (Completion v.1) (Fin 2)).sum_repr x]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  rw [Pi.basisFun_apply]
  exact s1513Single_mem_span G o v i

/-! ## 3. The actual binding record and its S1500 inhabitant -/

/-- The actual binding record: an actual S1402 source plus the integral image
generator family.  The lattice is defined from the image values, so it is
output-dependent whenever the image values are. -/
structure S1513HDDOutputBinding (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) where
  source : S1402DependentHDDSource I s
  generator : S1513ImageGeneratorFamily source

namespace S1513HDDOutputBinding

variable {I : Input Label Choice} {s : Finset (NumberField.FinitePlace ℚ)}

/-- The output-dependent rank-two local lattice family of a binding. -/
noncomputable def lattice (B : S1513HDDOutputBinding I s)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    Submodule (CompletionIntegers v.1) (Fin 2 → Completion v.1) :=
  s1513DiagonalLattice B.generator o v

/-- The S1500 target, inhabited from the actual image generator family. -/
noncomputable def toS1500 (B : S1513HDDOutputBinding I s) :
    S1500OutputDependentHDDLattice I s where
  source := B.source
  lattice := fun o v => s1513DiagonalLattice B.generator o v
  free := fun o v => s1513DiagonalLatticeFree B.generator o v
  finite := fun o v => s1513DiagonalLatticeFinite B.generator o v
  finrank := fun o v => s1513DiagonalLattice_finrank B.generator o v
  integral := fun o v => s1513DiagonalLattice_integral B.generator o v
  full := fun o v => s1513DiagonalLattice_span_eq_top B.generator o v
  imageGenerator := fun o v => B.generator.gen o v
  imageGenerator_mem := fun o v i => B.generator.mem o v i

@[simp] theorem toS1500_lattice (B : S1513HDDOutputBinding I s)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    (B.toS1500).lattice o v = s1513DiagonalLattice B.generator o v := rfl

/-- The local basis vector is exactly the actual image value placed in its
coordinate.  This is the actual binding, not a renamed free bundle. -/
theorem generatorVector_coord_eq_image (B : S1513HDDOutputBinding I s)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    s1513GeneratorVector B.generator o v i i = (B.generator.gen o v i) v := by
  simp [s1513GeneratorVector]

/-- Both local basis vectors are the actual image values at the selected
place, placed in their respective coordinates. -/
theorem generatorVector_eq_image (B : S1513HDDOutputBinding I s)
    (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (i : Fin 2) :
    s1513GeneratorVector B.generator o v i =
      Pi.single i ((B.generator.gen o v i) v) := rfl

end S1513HDDOutputBinding

/-! ## 4. The S1500 binding field alone does not enforce actual binding -/

/-- Under-specification witness, not the paper object: for any S1402 source,
the S1500 target is inhabited by the output-independent S1476 lattice.  The
imageGenerator_mem field is satisfied by an arbitrary chosen image point.
Thus the S1500 binding field alone does not force the lattice to be
output-dependent or to be generated by the image. -/
noncomputable def s1513OutputIndependentWitness
    (D : S1402DependentHDDSource I s) :
    S1500OutputDependentHDDLattice I s where
  source := D
  lattice := fun _ v => s1476LocalLattice 2 v.1
  free := fun _ v => s1476LocalLatticeFree 2 v.1
  finite := fun _ v => s1476LocalLatticeFinite 2 v.1
  finrank := fun _ v => s1476LocalLattice_finrank 2 v.1
  integral := fun _ v => s1476LocalLattice_integral 2 v.1
  full := fun _ v => s1476LocalLattice_span_eq_top 2 v.1
  imageGenerator := fun o _ _ => Classical.choose (D.nonempty o)
  imageGenerator_mem := fun o _ _ => Classical.choose_spec (D.nonempty o)

theorem s1513OutputIndependentWitness_lattice
    (D : S1402DependentHDDSource I s)
    (o o' : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    (s1513OutputIndependentWitness D).lattice o v =
      (s1513OutputIndependentWitness D).lattice o' v := rfl

/-- The S1500 target is satisfiable without output dependence, for every
source.  Hence its binding field is not by itself the actual paper binding. -/
theorem s1513S1500Target_does_not_force_output_dependence
    (D : S1402DependentHDDSource I s) :
    ∃ L : S1500OutputDependentHDDLattice I s,
      ∀ (o o' : Theorem311Output I)
        (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
        L.lattice o v = L.lattice o' v :=
  ⟨s1513OutputIndependentWitness D, fun _ _ _ => rfl⟩

/-! ## 5. The missing bound is not implied by the source fields -/

/-- A concrete S1402 source whose image is a singleton at an actual point,
with the det bookkeeping supplied as an explicit input.  The four image fields
of the source (compact_closure, nonempty, coordinate_nonzero, detData) are all
satisfied; nothing forces integrality of the image value. -/
noncomputable def s1513SingletonSource
    (x : S1513DependentPoint s)
    (hx : ∀ v, x v ≠ 0)
    (det : DetTensorPowerLogVolumeBookkeeping
      (Set (S1513DependentPoint s))) :
    S1402DependentHDDSource I s where
  image := fun _ => {x}
  compact_closure := fun _ => isCompact_singleton.closure
  nonempty := fun _ => ⟨x, rfl⟩
  coordinate_nonzero := fun _ v => ⟨x, rfl, hx v⟩
  detData := det

/-- If the singleton image has a non-integral coordinate, no integral image
generator family exists.  Therefore the S1402 image fields alone do not imply
the missing binding. -/
theorem s1513SingletonSource_no_generator
    (x : S1513DependentPoint s)
    (hx : ∀ v, x v ≠ 0)
    (det : DetTensorPowerLogVolumeBookkeeping
      (Set (S1513DependentPoint s)))
    (v0 : {v : NumberField.FinitePlace ℚ // v ∈ s})
    (hv0 : x v0 ∉ (CompletionIntegers v0.1 : Set (Completion v0.1))) :
    ¬ Nonempty (S1513ImageGeneratorFamily (I := I)
        (s1513SingletonSource (I := I) x hx det)) := by
  rintro ⟨G⟩
  let o : Theorem311Output I := theorem311Output I
  have hmem : G.gen o v0 0 ∈ (s1513SingletonSource x hx det).image o :=
    G.mem o v0 0
  have hgen : G.gen o v0 0 = x := by
    simpa [s1513SingletonSource] using hmem
  have hint : G.gen o v0 0 v0 ∈
      (CompletionIntegers v0.1 : Set (Completion v0.1)) :=
    G.integral o v0 0
  rw [hgen] at hint
  exact hv0 hint

/-- At every actual place there exists a non-integral element: the inverse of
a uniformizer, whose valuation is above one. -/
theorem s1513ExistsNonintegralElement
    (v0 : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    ∃ x : Completion v0.1,
      x ∉ (CompletionIntegers v0.1 : Set (Completion v0.1)) := by
  obtain ⟨q, hq0, hqlt⟩ := finitePlaceQCandidate_nonempty v0.1
  refine ⟨(q : Completion v0.1)⁻¹, ?_⟩
  have hqval_ne : Valued.v (q : Completion v0.1) ≠ 0 := by
    intro h
    exact hq0 (((Valued.v :
      Valuation (Completion v0.1) (WithZero (Multiplicative Int))).map_eq_zero_iff).mp h)
  have hqpos : 0 < Valued.v (q : Completion v0.1) :=
    lt_of_le_of_ne (zero_le : (0 : WithZero (Multiplicative Int)) ≤ Valued.v (q : Completion v0.1))
      (Ne.symm hqval_ne)
  have hone_lt : 1 < (Valued.v (q : Completion v0.1))⁻¹ :=
    one_lt_inv_iff₀.mpr ⟨hqpos, hqlt⟩
  intro hmem
  have hle : Valued.v ((q : Completion v0.1)⁻¹) ≤ 1 := hmem
  rw [map_inv₀] at hle
  exact not_le_of_gt hone_lt hle

/-! ## 6. Checks -/

#check S1513DependentPoint
#check S1513ImageGeneratorFamily
#check s1513LocalGenerator
#check s1513GeneratorVector
#check s1513DiagonalMap
#check s1513DiagonalLattice_eq_span
#check s1513DiagonalLattice
#check s1513DiagonalEquiv
#check s1513DiagonalLatticeFree
#check s1513DiagonalLatticeFinite
#check s1513DiagonalLattice_finrank
#check s1513DiagonalLattice_integral
#check s1513DiagonalLattice_span_eq_top
#check S1513HDDOutputBinding
#check S1513HDDOutputBinding.toS1500
#check S1513HDDOutputBinding.lattice
#check S1513HDDOutputBinding.generatorVector_coord_eq_image
#check s1513OutputIndependentWitness
#check s1513S1500Target_does_not_force_output_dependence
#check s1513SingletonSource
#check s1513SingletonSource_no_generator
#check s1513ExistsNonintegralElement

end LeanFormal.IUT.XiFPaper.S1513HDDOutputBindingActual
