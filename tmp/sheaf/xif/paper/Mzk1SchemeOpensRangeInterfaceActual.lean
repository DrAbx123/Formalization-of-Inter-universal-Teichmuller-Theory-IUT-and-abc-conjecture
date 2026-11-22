/- Scheme.Opens / opensRange 的显式 coercion 接口（供 π⁻¹ opensRange 等式使用）。
   目标：把 Opens 层等式降为集合层逐点（Opens.ext），并给出 opensRange 的显式集合形式。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual
open AlgebraicGeometry CategoryTheory

/-- `opensRange` 作为集合 = 映射的像集（显式 coercion 形式）。 -/
theorem opensRange_coe_eq_range {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    (f.opensRange : Set Y) = Set.range f := by
  ext y
  rw [Set.mem_range]
  exact Scheme.Hom.mem_opensRange

/-- 点属于 `opensRange` 的显式 iff。 -/
theorem mem_opensRange_iff {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] (y : Y) :
    y ∈ f.opensRange ↔ ∃ x, f x = y := Scheme.Hom.mem_opensRange

/-- 开集等式降为集合等式（`Opens.ext` 的显式双向形式）。 -/
theorem opens_eq_iff_coe_eq {X : Scheme} (U V : X.Opens) :
    U = V ↔ (U : Set X) = (V : Set X) :=
  ⟨fun h => by rw [h], fun h => TopologicalSpace.Opens.ext h⟩

/-- 两开集相等：集合层逐点证明。 -/
theorem opens_eq_of_forall_mem {X : Scheme} {U V : X.Opens}
    (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  TopologicalSpace.Opens.ext (Set.ext h)

#print axioms opensRange_coe_eq_range
#print axioms mem_opensRange_iff
#print axioms opens_eq_iff_coe_eq
#print axioms opens_eq_of_forall_mem
/-- **carrier-bridge**：局部化态射 `Spec R → Spec R[1/f]` 的 opensRange，
    以 `Spec R` 的 `basicOpen`（ΓSpecIso 形式）表示。 供 π⁻¹ / opens 层使用。 -/
theorem opensRange_localizationAway' {R : CommRingCat} (g : R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))).opensRange
      = (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv.hom g) := by
  rw [Scheme.Hom.opensRange_localizationAway, basicOpen_eq_of_affine]

/-- **Set 层桥**：`x` 落在局部化态射的 opensRange 中当且仅当 `x ∈ PrimeSpectrum.basicOpen g`。 -/
theorem primeBasicOpen_opensRange_coe {R : CommRingCat} (g : R) (x : Spec R) :
    x ∈ (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))).opensRange
      ↔ x ∈ PrimeSpectrum.basicOpen g := by
  rw [Scheme.Hom.opensRange_localizationAway]
  rfl

#print axioms opensRange_localizationAway'
#print axioms primeBasicOpen_opensRange_coe


end LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual