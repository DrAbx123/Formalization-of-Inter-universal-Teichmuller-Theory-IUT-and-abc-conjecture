import tmp.sheaf.xif.paper.S2339FbarFactorsActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2345RootSetEquivActual
open Polynomial NumberField
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
noncomputable def s2345P (f : (RingOfIntegers K)[X]) : K[X] :=
  f.map (algebraMap (RingOfIntegers K) K)
noncomputable def s2345ToFun (f : (RingOfIntegers K)[X]) (hmonic : f.Monic) :
    f.rootSet (RingOfIntegers L) →
      (s2345P f).rootSet L :=
  fun a => ⟨algebraMap (RingOfIntegers L) L a.1, by
    rw [Polynomial.mem_rootSet']
    constructor
    · have hmap : (s2345P f).map (algebraMap K L) =
          f.map (algebraMap (RingOfIntegers K) L) := by
        simp only [s2345P, Polynomial.map_map]
        rw [IsScalarTower.algebraMap_eq (RingOfIntegers K) K L]
      rw [hmap]
      exact (hmonic.map (algebraMap (RingOfIntegers K) L)).ne_zero
    · have ha := a.2
      rw [Polynomial.mem_rootSet'] at ha
      have hroot : (Polynomial.aeval a.1) f = 0 := ha.2
      rw [show s2345P f = f.map (algebraMap (RingOfIntegers K) K) from rfl]
      have hmap_aeval := Polynomial.aeval_map_algebraMap (R := RingOfIntegers K)
        (A := K) (B := L) (algebraMap (RingOfIntegers L) L a.1) f
      rw [hmap_aeval]
      rw [Polynomial.aeval_algebraMap_apply L a.1 f, hroot, map_zero]⟩
theorem s2345ToFun_bijective (f : (RingOfIntegers K)[X]) (hmonic : f.Monic) :
    Function.Bijective (s2345ToFun (K := K) (L := L) f hmonic) := by
  constructor
  · intro a b h
    apply Subtype.ext
    exact RingOfIntegers.coe_injective
      (congrArg (fun z : (s2345P f).rootSet L => z.1) h)
  · intro x
    have hx := x.2
    rw [Polynomial.mem_rootSet'] at hx
    have hrootK : (Polynomial.aeval x.1) f = 0 := by
      have hmap := Polynomial.aeval_map_algebraMap (R := RingOfIntegers K)
        (A := K) (B := L) x.1 f
      rw [← hmap]
      exact hx.2
    have hint : IsIntegral (RingOfIntegers K) x.1 :=
      ⟨f, hmonic, by simpa [Polynomial.aeval_def] using hrootK⟩
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff
      (A := RingOfIntegers L) (R := RingOfIntegers K) (B := L)).mp hint
    have hyroot : (Polynomial.aeval y) f = 0 := by
      apply RingOfIntegers.coe_injective
      rw [← Polynomial.aeval_algebraMap_apply L y f, hy]
      exact hrootK
    have hyrootset : y ∈ f.rootSet (RingOfIntegers L) := by
      rw [Polynomial.mem_rootSet']
      exact ⟨(hmonic.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))).ne_zero,
        hyroot⟩
    refine ⟨⟨y, hyrootset⟩, ?_⟩
    apply Subtype.ext
    exact hy
noncomputable def s2345RootSetEquiv (f : (RingOfIntegers K)[X]) (hmonic : f.Monic) :
    f.rootSet (RingOfIntegers L) ≃ (s2345P f).rootSet L :=
  Equiv.ofBijective (s2345ToFun (K := K) (L := L) f hmonic)
    (s2345ToFun_bijective (K := K) (L := L) f hmonic)
@[simp]
theorem s2345RootSetEquiv_apply (f : (RingOfIntegers K)[X]) (hmonic : f.Monic)
    (a : f.rootSet (RingOfIntegers L)) :
    ((s2345RootSetEquiv (K := K) (L := L) f hmonic a).1 : L) =
      algebraMap (RingOfIntegers L) L a.1 := rfl
#print axioms s2345ToFun_bijective
#print axioms s2345RootSetEquiv
end LeanFormal.IUT.XiFPaper.S2345RootSetEquivActual
end
