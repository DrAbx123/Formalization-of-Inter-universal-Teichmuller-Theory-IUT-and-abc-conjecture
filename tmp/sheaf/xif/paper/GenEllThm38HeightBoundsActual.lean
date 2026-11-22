import Mathlib.Tactic

/-! # GenEllThm38HeightBoundsActual — GenEll Thm 3.8 effective bounds: statement/physical layer (class B)

STEP 0 prior-art (deep search + asset check 2026-11-10): pinned Mathlib has
Mathlib/NumberTheory/Height/{Basic,EllipticCurve,MvPolynomial,Northcott,NumberField,
Projectivization}.lean — not imported by the tree yet:
* Height/Basic: class AdmissibleAbsValues, mulHeight₁, logHeight₁, mulHeight, logHeight;
* Height/EllipticCurve: abs_logHeight_addSubMap_sub_two_mul_logHeight_le;
* Height/Northcott: Northcott finiteness API; Height/Projectivization: logHeight on P^1.
Ported FLT assets (tmp/external/ported/flt/Definitions/, EXIT=0 raw):
* Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean:19 structure FiniteMapData
(finite map to P^1 over a base; ranges/covers), :61-92 cover lemmas;
* Def_AlgebraicGeometry_SmoothProperCurveBase.lean: section base change;
* Def_AlgebraicCurve_RiemannRochRows.lean:19-47 Prop defs RiemannInequality,
RiemannIndexFormula, WeilDualityAdelic, WeilDuality, FunctionFieldRiemannRoch + :54/:59
reduction theorems; Def_AlgebraicCurve_SerrePairing.lean (263 lines, residue/cup
pairing lemmas); Def_AlgebraicCurve_CechSectionsOfDivisor.lean;
Def_AlgebraicCurve_DivisorClassGroup.lean; Def_AlgebraicCurve_AdelicIndex.lean.
Tree status of ported files: raw adaptation only in tmp/external/ported (S3171Ids:
6 adapted AG_FLT_* counted; RiemannRochRows/SerrePairing/SmoothProperCurveFiniteMapData
PENDING, not counted).

PAPER: [GenEll] §3; Prop 3.4 (Faltings heights) lines 994-1010; Lemma 3.5 (1011-1027);
Lemma 3.7 (1052-1144); Theorem 3.8 (1145-1166) with effective constants
23040 = (3^2-1)(3^2-3)(5^2-1)(5^2-5) and l >= 23040 * 100d * (ht_Falt([E_L]) + C d^eps).

DELIVERABLE OF THIS FILE: the statement/physical layer record for the Thm 3.8 bounds
(class B, no proof): which quantities are available from Mathlib Height + ported
assets, which remain paper-input, and the exact identification plan.  NOT counted as
progress until the height layer is instantiated; no fake proof. -/

namespace LeanFormal.IUT.XiFPaper.GenEllThm38HeightBoundsActual

structure GenEllHeightAssetRow where
  need : String
  availableAsset : String
  status : String

def genEllThm38HeightAssets : List GenEllHeightAssetRow :=
  [ ⟨"canonical height ht (logHeight of a projective point/line bundle)", "Mathlib.NumberTheory.Height.Basic: AdmissibleAbsValues, mulHeight, logHeight, mulHeight₁, logHeight₁; Height.Projectivization.logHeight", "AVAILABLE (Mathlib, needs import; class A physical layer)"⟩,
    ⟨"height algebra ht_{L tensor M} = ht_L + ht_M (GenEll Prop 1.4 (i))", "Height.Basic definitions + Mathlib Additive/Height API", "ADAPT (class A; compare our S3131BDClass* files)"⟩,
    ⟨"Northcott finiteness (bounded height + bounded degree => finite)", "Mathlib.NumberTheory.Height.Northcott", "AVAILABLE (class A physical layer)"⟩,
    ⟨"ht_Falt (Faltings height) and the chain deg_inf <~ ht_inf <~ 12(1+eps) ht_Falt <~ (1+eps) ht_inf (Prop 3.4)", "NOT in Mathlib (no Faltings height); paper input [Silv2] Proposition 2.1", "PAPER-INPUT (class B); statement shape recorded in GenEll06Section3StatementsActual"⟩,
    ⟨"log-diff/log-cond functions (GenEll Def 1.5)", "NOT in Mathlib; ported FLT Def_AlgebraicCurve_LocalResidue/RegularDifferentials give local residue/differential layers", "ADAPT-PENDING (ported raw; not counted)"⟩,
    ⟨"l-cyclic subgroup schemes / semistable reduction (Lemma 3.2/3.5)", "NOT in Mathlib; ported Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData/Base are scheme-level but no semi-abelian schemes", "PAPER-INPUT (class B)"⟩,
    ⟨"SL2(Z_l) image/Serre large-image input (Thm 3.8 conclusion)", "S1907SerreLargeImageActual (tree source form); Mathlib Matrix/GL/SL API", "REUSE S1907 for statement; analytic input [Serre] remains paper-input"⟩,
    ⟨"effective constants 23040 = (3^2-1)(3^2-3)(5^2-1)(5^2-5); 100d; C d^eps", "elementary arithmetic (class A): 23040 = 8*6*24*20 numerically verifiable", "FORMALIZABLE NOW (Nat arithmetic), record in GenEll06 rows"⟩ ]

theorem genEllThm38HeightAssets_length : genEllThm38HeightAssets.length = 8 := rfl

/-- The class-A effective constant identity 23040 = (3^2-1)(3^2-3)(5^2-1)(5^2-5). -/
theorem genEllThm38_23040_eq : (3 ^ 2 - 1) * (3 ^ 2 - 3) * (5 ^ 2 - 1) * (5 ^ 2 - 5) = 23040 := by
  norm_num

#check genEllThm38_23040_eq
#check genEllThm38HeightAssets_length

end LeanFormal.IUT.XiFPaper.GenEllThm38HeightBoundsActual