import tmp.sheaf.xif.paper.S2650FiveDivisionEmbeddingActual
import tmp.sheaf.xif.paper.S2494bRootCycleTypeMod29Actual

noncomputable section
set_option maxHeartbeats 4000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2650FiveDivisionEmbeddingActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual

namespace LeanFormal.IUT.XiFPaper.S2651RootMapActual

variable (f : (RingOfIntegers S1720Field)[X])
  (c : S1720Field) (hc : c ≠ 0)
  (hK : f.map (algebraMap (RingOfIntegers S1720Field) S2056K) =
    Polynomial.C (algebraMap S1720Field S2056K c) * (S2056W.preΨ (5 : ℤ)))

theorem S2651_mem_rootFinset (x : S2056K)
    (hx : Polynomial.aeval x (S2056W.preΨ (5 : ℤ)) = 0) :
    x ∈ S2056RootFinset := by
  rw [S2056RootFinset, Multiset.mem_toFinset,
    Polynomial.mem_roots S2056W_preΨ_ne_zero, Polynomial.IsRoot.def]
  exact hx

instance : NumberField S2057FiveDivisionField where
  to_charZero := inferInstance
  to_finiteDimensional :=
    FiniteDimensional.trans ℚ S1720Field S2057FiveDivisionField

noncomputable def S2651RootMap
    (f : (RingOfIntegers S1720Field)[X]) (c : S1720Field) (hc : c ≠ 0)
    (hK : f.map (algebraMap (RingOfIntegers S1720Field) S2056K) =
      Polynomial.C (algebraMap S1720Field S2056K c) *
        (S2056W.preΨ (5 : ℤ))) :
    f.rootSet (RingOfIntegers S2057FiveDivisionField) → S2056Root := by
  intro a
  let φ : RingOfIntegers S2057FiveDivisionField →+* S2056K :=
    S2650Embedding.toRingHom.comp
      (algebraMap (RingOfIntegers S2057FiveDivisionField) S2057FiveDivisionField)
  refine ⟨S2650Embedding
      (algebraMap (RingOfIntegers S2057FiveDivisionField) S2057FiveDivisionField a.1),
    S2651_mem_rootFinset
      (S2650Embedding
        (algebraMap (RingOfIntegers S2057FiveDivisionField) S2057FiveDivisionField a.1)) ?_⟩
  have ha : Polynomial.aeval a.1 f = 0 :=
    (Polynomial.mem_rootSet'.mp a.2).2
  have hmap := Polynomial.map_aeval_eq_aeval_map
    (R := RingOfIntegers S1720Field)
    (S := RingOfIntegers S2057FiveDivisionField)
    (T := S2056K) (U := S2056K)
    (φ := algebraMap (RingOfIntegers S1720Field) S2056K)
    (ψ := φ) (p := f) (a := a.1)
    (by
      ext x
      simp only [RingHom.comp_apply, RingHom.id_apply]
      change algebraMap (RingOfIntegers S1720Field) S2056K x =
        S2650Embedding (algebraMap (RingOfIntegers S2057FiveDivisionField)
          S2057FiveDivisionField (algebraMap (RingOfIntegers S1720Field)
            (RingOfIntegers S2057FiveDivisionField) x))
      rw [← IsScalarTower.algebraMap_apply (RingOfIntegers S1720Field)
        (RingOfIntegers S2057FiveDivisionField) S2057FiveDivisionField]
      exact (S2650Embedding.commutes x).symm)
  have hmap0 : Polynomial.aeval (φ a.1)
      (f.map (algebraMap (RingOfIntegers S1720Field) S2056K)) = 0 := by
    rw [← hmap, ha, map_zero]
  rw [hK, map_mul] at hmap0
  simp only [Polynomial.aeval_C, Polynomial.aeval_X] at hmap0
  have hc' : algebraMap S1720Field S2056K c ≠ 0 := by
    intro h
    exact hc ((algebraMap S1720Field S2056K).injective (by simpa using h))
  have : Polynomial.aeval (S2650Embedding
      (algebraMap (RingOfIntegers S2057FiveDivisionField) S2057FiveDivisionField a.1))
      (S2056W.preΨ (5 : ℤ)) = 0 :=
    (mul_eq_zero.mp hmap0).resolve_left hc'
  exact this


theorem S2651RootMap_injective
    (f : (RingOfIntegers S1720Field)[X]) (c : S1720Field) (hc : c ≠ 0)
    (hK : f.map (algebraMap (RingOfIntegers S1720Field) S2056K) =
      Polynomial.C (algebraMap S1720Field S2056K c) *
        (S2056W.preΨ (5 : ℤ))) :
    Function.Injective (S2651RootMap f c hc hK) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  have he := S2650Embedding.injective h
  exact Subtype.ext (IsFractionRing.injective
    (RingOfIntegers S2057FiveDivisionField) S2057FiveDivisionField he)

#check S2651RootMap
#check S2651RootMap_injective


end LeanFormal.IUT.XiFPaper.S2651RootMapActual
end
