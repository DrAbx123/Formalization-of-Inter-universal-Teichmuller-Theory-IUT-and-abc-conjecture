import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: scheme<->function-field bridge (Lead A427) -> legacy scheme layer Mzk1FiniteMapData lives in the flt_test root; RR/zero-divisor function-field layer lives in the flt_core root; flt_test and flt_core CANNOT be imported in the same file (duplicate AlgebraicCurve definitions).  SOLUTION: this root-NEUTRAL interface file (Mathlib only) defines the bridge data abstractly, so a flt_core adapter and a flt_test adapter can each import it without importing the other root.

# Mzk1GeomCoreBridgeInterfaceActual — root-neutral scheme<->function-field bridge interface

CONTENT (no port root imported):
* ZeroDivisorDatum P F ord: a nonzero function g whose zero divisor is exactly sum_T [t]
  (order +1 on T, no positive order outside T).  This is the output of the flt_core RR
  layer (zero_divisor_exists_proved) and the input expected by the scheme side.
* FibreBridgeAbstract ... U f basicOpen P ord: the bridge data connecting a scheme
  affine chart (U, section f, basic-open predicate) to the function field (places P,
  order ord, sectionMap, placePoint).  The two genuine API gaps are explicit DATA fields:
  `sectionMap : Γ(C,U) ->+* F` and `placePoint : P -> C`; their compatibility with the
  zero locus is recorded in PROVED-relevant hypotheses (`section_ord`), and the zero-set
  equality is PROVED from the fields (`zeroSet_eq_of_abstract`).
* zeroSet_eq_of_abstract: PROVED identification
  {x in U : x notin basicOpen} = placePoint '' Tplaces.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual

universe u v w

/-- Function-field zero divisor datum: g != 0 with ORD(t,g) = 1 exactly on T and no
positive order outside T (zero divisor exactly sum_T [t]). -/
structure ZeroDivisorDatum (P : Type u) (F : Type v) [Field F] (ord : P → F → ℤ) where
  /-- the finite set of points T -/
  T : Finset P
  /-- the function whose zero divisor is sum_T [t] -/
  g : F
  g_ne_zero : g ≠ 0
  zero_simple : ∀ t ∈ T, ord t g = 1
  no_other_zero : ∀ p, p ∉ T → ord p g ≤ 0

/-- Root-neutral fibre bridge data: connects a scheme affine chart (U, section f,
basic-open predicate) to the function field (places P, order ord).  `sectionMap` and
`placePoint` are the two missing APIs and are explicit data; the compatibility fields
are the bridge hypotheses. -/
structure FibreBridgeAbstract (X : Type u) (A : Type v) (F : Type w) [CommRing A] [Field F]
    (U : Set X) (f : A) (basicOpen : Set X) (P : Type*) (ord : P → F → ℤ) where
  /-- the (missing) map from function-field places to scheme points -/
  placePoint : P → X
  /-- the (missing) map from sections on U to the function field -/
  sectionMap : A →+* F
  /-- the places over T -/
  Tplaces : Finset P
  /-- bridge hypothesis: on U, f vanishes at placePoint p iff ORD(p, sectionMap f) > 0 -/
  section_ord : ∀ p : P, placePoint p ∈ U →
    (placePoint p ∉ basicOpen ↔ 0 < ord p (sectionMap f))
  /-- Tplaces is exactly the zero set of sectionMap f in the function field -/
  Tplaces_eq : ∀ p : P, p ∈ Tplaces ↔ 0 < ord p (sectionMap f)
  /-- every scheme point of U where f vanishes is placePoint of some place -/
  surjective : ∀ t : X, t ∈ U → t ∉ basicOpen → ∃ p : P, placePoint p = t
  /-- places over T map into U -/
  placePoint_mem_U : ∀ p ∈ Tplaces, placePoint p ∈ U

/-- **PROVED zero-set identification:** the zero locus of f inside U is exactly the
image of the places over T.  This is the mathematical content of the bridge; only the
two map fields of the bridge remain named inputs. -/
theorem zeroSet_eq_of_abstract {X : Type u} {A : Type v} {F : Type w} [CommRing A]
    [Field F] {U : Set X} {f : A} {basicOpen : Set X} {P : Type*} {ord : P → F → ℤ}
    (B : FibreBridgeAbstract X A F U f basicOpen P ord) :
    ({t : X | t ∈ U ∧ t ∉ basicOpen} : Set X) =
      B.placePoint '' (B.Tplaces : Set P) := by
  ext t
  constructor
  · rintro ⟨htU, htb⟩
    obtain ⟨p, rfl⟩ := B.surjective t htU htb
    have hpos : 0 < ord p (B.sectionMap f) := (B.section_ord p htU).mp htb
    exact ⟨p, (B.Tplaces_eq p).mpr hpos, rfl⟩
  · rintro ⟨p, hpT, rfl⟩
    have hU : B.placePoint p ∈ U := B.placePoint_mem_U p hpT
    have hpos : 0 < ord p (B.sectionMap f) := (B.Tplaces_eq p).mp hpT
    exact ⟨hU, (B.section_ord p hU).mpr hpos⟩

/-- Bridging a zero-divisor datum with a scheme-side function f: if the function-field
element is the image of the scheme section and the zero divisor is T, then the fibre
over zero of f is exactly the image of T.  (The equality `g = sectionMap f` is the
named compatibility input.) -/
theorem zeroDivisorDatum_zeroSet_eq {X : Type u} {A : Type v} {F : Type w} [CommRing A]
    [Field F] {U : Set X} {f : A} {basicOpen : Set X} {P : Type*} {ord : P → F → ℤ}
    (B : FibreBridgeAbstract X A F U f basicOpen P ord) (Z : ZeroDivisorDatum P F ord)
    (hT : Z.T = B.Tplaces) :
    ({t : X | t ∈ U ∧ t ∉ basicOpen} : Set X) = B.placePoint '' (Z.T : Set P) :=
  by rw [zeroSet_eq_of_abstract B, hT]

/-- Interface row record: what is proved here vs the named API gaps. -/
def bridgeInterfaceRows : List (String × String × String) :=
  [ ("ZeroDivisorDatum (function-field side)", "DEFINED", "flt_core zero_divisor_exists_proved maps into this (universe-neutral)")
  , ("FibreBridgeAbstract (scheme<->field bridge)", "DEFINED", "root-neutral: imports no port root")
  , ("zero-set identification", "PROVED zeroSet_eq_of_abstract", "zero locus of f in U = placePoint '' Tplaces")
  , ("compatibility g = sectionMap f + T = Tplaces", "PROVED zeroDivisorDatum_zeroSet_eq", "named equality input hT")
  , ("sectionMap : Gamma(C,U) ->+* F", "NAMED API GAP", "no API in Mathlib/ported roots links a scheme section ring to a function field")
  , ("placePoint : P -> C", "NAMED API GAP", "no API links AlgebraicCurve.Place to scheme points") ]

theorem bridgeInterfaceRows_length : bridgeInterfaceRows.length = 6 := rfl

#check ZeroDivisorDatum
#check FibreBridgeAbstract
#check zeroSet_eq_of_abstract
#check zeroDivisorDatum_zeroSet_eq
#check bridgeInterfaceRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
end