/- Port LANA Concrete/Invariants.lean (Mathlib+ported Places/GlobalField):
  twoTorsionXOf (:196), tripodalFieldOf (:203), IsBadTpdOf (:214), logConductorDegOf (:221);
  donor path: tmp/lana-port-src/Iut/Concrete/Invariants.lean, ported deps:
  tmp/sheaf/lana/iut/Iut/Cor312/ThetaData/{Places,GlobalField}.lean (Iut.fieldOfModuli/Iut.badPlacesOver/
  Iut.FinitePlace.LiesOver/Iut.Place.LiesOver)。改法: lana 自建 FinitePlace 扩展 → 用 ported Iut.*;
  absNorm 显式转 ℝ; 不用 lana 的 Place.finite 别名以外的私有件。

  另: hsQ 的 s^Q 对象（distinct rational primes primorial, IV L1485-1501 口径）:
  sQOf S := ∏ p∈S p; log_sQOf_eq: log sQ = Σ log p; sQOf_pos。 -/
import tmp.sheaf.xif.paper.lana.iut.Iut.Cor312.ThetaData.GlobalField
import tmp.sheaf.xif.paper.Mzk1ULTripodalFieldActual
import tmp.sheaf.xif.paper.Mzk1ULPointConductorActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual

open NumberField

universe u

section Tripodal

variable (F : Type u) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

/-- E 的 2-torsion x-坐标（lana Invariants:196）。 -/
def twoTorsionXOf : Set F :=
  {a | ∃ (b : F) (h : E.toAffine.Nonsingular a b),
    WeierstrassCurve.Affine.Point.some a b h ∈ AddSubgroup.torsionBy E.toAffine.Point 2}

/-- F_tpd = F_mod(E[2])（lana Invariants:203）。 -/
noncomputable def tripodalFieldOf : IntermediateField ℚ F :=
  IntermediateField.adjoin ℚ (insert E.j (twoTorsionXOf F E))

instance tripodalFieldOf_finiteDimensional : FiniteDimensional ℚ ↥(tripodalFieldOf F E) :=
  Module.Finite.left ℚ ↥(tripodalFieldOf F E) F

instance tripodalFieldOf_numberField : NumberField ↥(tripodalFieldOf F E) where

/-- 定义展开（rfl）。 -/
theorem tripodalFieldOf_eq :
    tripodalFieldOf F E = IntermediateField.adjoin ℚ (insert E.j (twoTorsionXOf F E)) := rfl

/-- F_mod ⊆ F_tpd。 -/
theorem fieldOfModuli_le_tripodalFieldOf : Iut.fieldOfModuli F E ≤ tripodalFieldOf F E := by
  unfold Iut.fieldOfModuli tripodalFieldOf
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (IntermediateField.subset_adjoin (F := ℚ) (S := insert E.j (twoTorsionXOf F E))) (by simp)

variable (VBad : Set (FinitePlace ↥(Iut.fieldOfModuli F E)))

/-- F_tpd 的坏位（lana Invariants:214）。 -/
def IsBadTpdOf (𝔭 : FinitePlace ↥(tripodalFieldOf F E)) : Prop :=
  ∃ w ∈ Iut.badPlacesOver F E VBad,
    Iut.Place.LiesOver (k := ↥(tripodalFieldOf F E)) (K := F)
      (Iut.Place.finite w) (Iut.Place.finite 𝔭)

/-- log f_Ftpd（lana Invariants:221）。 -/
noncomputable def logConductorDegOf : ℝ :=
  (∑ᶠ 𝔭 : FinitePlace ↥(tripodalFieldOf F E),
    if IsBadTpdOf F E VBad 𝔭 then
      Real.log ((Ideal.absNorm (𝔭.maximalIdeal).asIdeal : ℕ) : ℝ) else 0) /
    (Module.finrank ℚ ↥(tripodalFieldOf F E) : ℝ)

/-- 非负。 -/
theorem logConductorDegOf_nonneg : 0 ≤ logConductorDegOf F E VBad := by
  unfold logConductorDegOf
  apply div_nonneg _ (by positivity)
  apply finsum_nonneg
  intro 𝔭
  split_ifs
  · exact Real.log_natCast_nonneg _
  · exact le_rfl

end Tripodal

/-- s^Q 的 rational-prime 部分（distinct primes primorial, IV L1485-1501）。 -/
noncomputable def sQOf (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- log s^Q = Σ log p。 -/
theorem log_sQOf_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) :
    Real.log (sQOf S : ℝ) = ∑ p ∈ S, Real.log (p : ℝ) := by
  unfold sQOf
  have h : ((∏ p ∈ S, p : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := by push_cast; rfl
  rw [h]
  exact Real.log_prod (s := S) (f := fun p : ℕ => (p : ℝ))
    (fun p hp => by exact_mod_cast hS p hp)

/-- s^Q > 0。 -/
theorem sQOf_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) : 0 < sQOf S := by
  unfold sQOf
  exact Finset.prod_pos (fun p hp => Nat.pos_of_ne_zero (hS p hp))

end LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual