import tmp.sheaf.lana_latest.Iut.Frobenioid.Thm51
import tmp.sheaf.lana_latest.Iut.Frobenioid.KummerClass

/-! Mainline (A514-1): reference/adapter file for the LANA-latest Frobenioid objects and
theorems ([FrdI] Thm 5.1, [FrdII] Def 2.1(ii)) used by Theorem 3.11's O1 (prime-strip /
Frobenioid side).  The objects are the real LANA declarations; this file re-exports them
under our namespace with an O1 record and the Kummer-class operators, without copying the
large implementation files. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LanaLatestFrobenioidActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open CategoryTheory
open scoped IsMulCommutative

universe w v u

section FrobenioidObjects

variable {D : Type u} [Category.{v} D]
variable {Φ : Iut.Frobenioid.DivMonoid.{w} D} {B : Iut.Frobenioid.GrpOn.{w} D}
variable {divB : Iut.Frobenioid.DivHom B Φ.toGrpOn}

/-- **O1 object**: a model-Frobenioid object `(A_D, α)` ([FrdI] Theorem 5.2(i)) used as the
  value/Frobenius side of the prime-strip data in Theorem 3.11. -/
structure FrobenioidObject where
  /-- The underlying model-Frobenioid object `(A_D, α)`. -/
  model : Iut.Frobenioid.Model Φ B divB

/-- The divisor `α ∈ Φ^gp(A_D)` of the object. -/
def FrobenioidObject.divisor (X : FrobenioidObject (Φ := Φ) (B := B) (divB := divB)) :
    Φ.obj X.model.base :=
  X.model.α

/-- **[FrdI] Theorem 5.1(ii)** (re-exported): a morphism of Frobenius degree `d`, projection
  `θ` and zero divisor `z` exists iff `d·α + z ≡ θ^*β` modulo `Div_B(B)`. -/
theorem frobenioid_exists_hom_iff (X Y : Iut.Frobenioid.Model Φ B divB) (d : ℕ+)
    (θ : X.base ⟶ Y.base) {z : Φ.obj X.base} (hz : z ∈ Φ.pos X.base) :
    (∃ φ : X ⟶ Y, φ.deg = d ∧ φ.base = θ ∧ φ.div = z) ↔
      ∃ u : B.obj X.base,
        (d : ℕ) • X.α + z - Φ.pb θ Y.α = divB.app X.base u :=
  Iut.Frobenioid.Model.exists_hom_iff X Y d θ hz

/-- **[FrdI] Theorem 5.1(ii)** uniqueness of the unit-equivalence class (re-exported). -/
theorem frobenioid_toElem_map_eq_of {X Y : Iut.Frobenioid.Model Φ B divB}
    {φ ψ : X ⟶ Y} (h₁ : φ.deg = ψ.deg) (h₂ : φ.base = ψ.base) (h₃ : φ.div = ψ.div) :
    (Iut.Frobenioid.Model.toElem Φ B divB).map φ =
      (Iut.Frobenioid.Model.toElem Φ B divB).map ψ :=
  Iut.Frobenioid.Model.toElem_map_eq_of h₁ h₂ h₃

/-- **[FrdI] Theorem 5.1(i)** (re-exported): a base-identity Frobenius-type morphism
  multiplies the class by `degFr`. -/
theorem frobenioid_class_frobeniusType {X Y : Iut.Frobenioid.Model Φ B divB}
    (κ : X ⟶ Y) (hb : X.base = Y.base) (hκ : κ.base = eqToHom hb) (h0 : κ.div = 0) :
    ∃ u : B.obj X.base,
      (κ.deg : ℕ) • X.α - Φ.pb (eqToHom hb) Y.α = divB.app X.base u :=
  Iut.Frobenioid.Model.class_frobeniusType κ hb hκ h0

end FrobenioidObjects

section KummerClasses

variable {G : Type*} [Group G]
variable (U : Subgroup G) [U.Normal] [IsMulCommutative U] (H : Subgroup G) (n : ℕ)
variable [TopologicalSpace G] [DiscreteTopology G]

/-- **O1/O5 Kummer roots**: `μ_n(U) = {u ∈ U | u^n = 1}` ([FrdII] Def 2.1(ii)). -/
def kummerMu : Subgroup U :=
  Iut.Frobenioid.KummerClass.mu U n

@[simp] theorem mem_kummerMu_iff {u : U} : u ∈ kummerMu U n ↔ u ^ n = 1 :=
  Iff.rfl

/-- **The Kummer class** `κ ∈ H¹(H, μ_n(U))` of an `N`-th root `g` ([FrdII] Def 2.1(ii),
  the cohomological datum used by the Θ-pilot Kummer classes in Theorem 3.11). -/
def kummerClass (g : U)
    (hg : ∀ h ∈ H, Iut.Frobenioid.KummerClass.conjU U h (g ^ n) = g ^ n) :
    ContH1 H (kummerMu U n) :=
  Iut.Frobenioid.KummerClass.kummerClass U H n g hg

/-- **Independence of the Kummer root** ([FrdII] Def 2.1(ii), re-exported). -/
theorem kummerClass_eq_of_pow_eq (g g' : U)
    (hg : ∀ h ∈ H, Iut.Frobenioid.KummerClass.conjU U h (g ^ n) = g ^ n)
    (hg' : ∀ h ∈ H, Iut.Frobenioid.KummerClass.conjU U h (g' ^ n) = g' ^ n)
    (hpow : g ^ n = g' ^ n) :
    kummerClass U H n g hg = kummerClass U H n g' hg' :=
  Iut.Frobenioid.KummerClass.kummerClass_eq_of_pow_eq U H n g g' hg hg' hpow

end KummerClasses

end

end LeanFormal.IUT.XiFPaper.Mzk1LanaLatestFrobenioidActual