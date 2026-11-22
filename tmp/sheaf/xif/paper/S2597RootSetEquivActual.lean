import tmp.sheaf.xif.paper.S2539AbstractRedRootActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual

variable {R S K L : Type*}
  [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [Algebra S L] [Algebra R S]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsFractionRing R K]
  [FaithfulSMul R L] [IsIntegralClosure S R L]

variable (f : R[X]) (hmonic : f.Monic) (hdeg : f.natDegree ≠ 0)

/-- Send an L-root into the integral closure S. -/
noncomputable def toS (a : f.rootSet L) : f.rootSet S := by
  classical
  have hroot : aeval a.1 f = 0 := (mem_rootSet'.mp a.2).2
  have hint : IsIntegral R a.1 := by
    apply IsIntegral.of_aeval_monic hmonic hdeg
    rw [hroot]
    exact isIntegral_zero
  let y : S := Classical.choose
    ((IsIntegralClosure.isIntegral_iff (A := S) (R := R) (B := L)).mp hint)
  have hy : algebraMap S L y = a.1 := Classical.choose_spec
    ((IsIntegralClosure.isIntegral_iff (A := S) (R := R) (B := L)).mp hint)
  refine ⟨y, ?_⟩
  rw [mem_rootSet']
  constructor
  · exact Polynomial.map_monic_ne_zero hmonic
  · apply IsIntegralClosure.algebraMap_injective S R L
    rw [map_zero]
    calc algebraMap S L (aeval y f)
        = aeval (algebraMap S L y) (f.map (algebraMap R S)) :=
          Polynomial.map_aeval_eq_aeval_map (φ := algebraMap R S) (ψ := algebraMap S L) rfl f y
      _ = aeval (algebraMap S L y) (f.map (algebraMap R L)) := by
          let z := algebraMap S L y
          calc aeval z (f.map (algebraMap R S))
              = aeval z f :=
                (Polynomial.aeval_map_algebraMap (A := S) (B := L) z f)
            _ = aeval z (f.map (algebraMap R L)) :=
                (Polynomial.aeval_map_algebraMap (A := L) (B := L) z f).symm

      _ = aeval a.1 (f.map (algebraMap R L)) := by rw [hy]
      _ = 0 := by
          rw [Polynomial.aeval_map_algebraMap L]
          exact hroot


lemma toS_val (a : f.rootSet L) :
    algebraMap S L (toS (R := R) (S := S) (L := L) f hmonic hdeg a).1 = a.1 := by
  classical
  unfold toS
  dsimp
  exact Classical.choose_spec
    ((IsIntegralClosure.isIntegral_iff (A := S) (R := R) (B := L)).mp (by
      apply IsIntegral.of_aeval_monic hmonic hdeg
      rw [(mem_rootSet'.mp a.2).2]
      exact isIntegral_zero))

lemma toS_injective : Function.Injective
    (toS (R := R) (S := S) (L := L) f hmonic hdeg) := by
  intro a b h
  apply Subtype.ext
  have hy : (toS (R := R) (S := S) (L := L) f hmonic hdeg a).1 =
      (toS (R := R) (S := S) (L := L) f hmonic hdeg b).1 :=
    congrArg Subtype.val h
  calc a.1 = algebraMap S L (toS (R := R) (S := S) (L := L) f hmonic hdeg a).1 :=
        (toS_val f hmonic hdeg a).symm
    _ = algebraMap S L (toS (R := R) (S := S) (L := L) f hmonic hdeg b).1 := by rw [hy]
    _ = b.1 := toS_val f hmonic hdeg b

/-- Conditional bijectivity, with the L-root-cardinality hypothesis. -/
lemma toS_bijective (hcardS : Fintype.card (f.rootSet S) = f.natDegree)
    (hcardL : Fintype.card (f.rootSet L) = f.natDegree) :
    Function.Bijective (toS (R := R) (S := S) (L := L) f hmonic hdeg) := by
  have hcard : Fintype.card (f.rootSet L) = Fintype.card (f.rootSet S) := by
    rw [hcardL, hcardS]
  exact (Fintype.bijective_iff_injective_and_card (f := toS (R := R) (S := S) (L := L) f hmonic hdeg)).mpr
    ⟨toS_injective f hmonic hdeg, hcard⟩



/-- The root-set equivalence, conditional on the two cardinality facts. -/
noncomputable def rootSetEquivLT (hcardS : Fintype.card (f.rootSet S) = f.natDegree)
    (hcardL : Fintype.card (f.rootSet L) = f.natDegree) :
    f.rootSet L ≃ f.rootSet S :=
  Equiv.ofBijective (toS (R := R) (S := S) (L := L) f hmonic hdeg)
    (toS_bijective f hmonic hdeg hcardS hcardL)


end LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual
end