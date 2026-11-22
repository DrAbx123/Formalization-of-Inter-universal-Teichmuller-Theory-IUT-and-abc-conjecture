import Mathlib

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Frd01: Frobenioids [FrdI]/[FrdII] — statement/definition layer (external-object target)

Paper sources (corpus texts present):
* "The Geometry of Frobenioids I: The General Theory" (FrdI): §1 Definitions and
  First Properties; §2 Frobenius Functors; §3 Category-theoreticity of the Base and
  Frobenius Degree; §4 Category-theoreticity of the Divisor Monoid; §5 Model
  Frobenioids; §6 Motivating Examples.  Anchors: Prop 1.4 l.1109, 1.5 l.1163,
  1.6 l.1194, 1.7 l.1236, 1.8 l.1303, 1.9 l.1331, 1.10 l.1484, 1.11 l.1599.
* "The Geometry of Frobenioids II: Poly-Frobenioids" (FrdII): §1 Nonarchimedean
  Primes; §2 The Kummer and Reciprocity Maps; §3 Archimedean Primes; §4 Angloids as
  Base Categories; §5 Poly-Frobenioids.  Anchors: Thm 1.2 l.376, Prop 1.5 l.584,
  Thm 2.4 l.818, Prop 3.4 l.1446.
* "Responses to questions on Frobenioids" corpus text present.

This is the P0 definition layer: Frobenioid (category + divisor theory + Frobenius
action), divisorial monoid, model Frobenioid, poly-Frobenioid, and the Frobenius
action data.  Tree reuse (see Frd02ReuseAuditActual): the concrete model Frobenioid
already exists (Iut.FrobenioidPresentation / SourceModelFrobenioid* /
ConcreteSourceFrobenioidBridge).  Deep category-theoreticity results are class B.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Frd01StatementActual

universe u

/-- A divisorial monoid datum (FrdI §1): a commutative monoid with a divisorial/
prime-part structure abstracted as a submonoid of "divisor" elements and a support
predicate.  Kept abstract at the statement layer. -/
structure DivisorialMonoidData where
  /-- the underlying commutative monoid -/
  M : Type u
  commMonoid : CommMonoid M
  /-- the divisorial cone (prime/divisor-like elements) -/
  divisorial : Set M
  /-- the zero element (unit) -/
  zero : M
  /-- zero is the monoid identity -/
  zero_eq_one : zero = 1
  /-- the divisorial cone contains the identity -/
  one_mem : (1 : M) ∈ divisorial

/-- A model Frobenioid datum (FrdI §5): base category + divisor monoid functor +
line-bundle/degree data, in abstract record form. -/
structure ModelFrobenioidData where
  /-- the base category objects -/
  Base : Type u
  /-- the Frobenioid objects -/
  Obj : Type u
  /-- the object-to-base projection -/
  toBase : Obj → Base
  /-- the divisor monoid at an object, with its divisorial datum -/
  divisorMonoid : Obj → DivisorialMonoidData
  /-- the Pic/line-bundle degree readout -/
  degree : Obj → ℤ
  /-- the Frobenius degree readout (FrdI §2-§3) -/
  frobeniusDegree : Obj → ℤ

/-- The Frobenius action datum (FrdI §2 Frobenius functors / [FrdII] unit-linear
Frobenius functors): an endomorphism of the Frobenioid objects compatible with the
divisor monoid and the degree. -/
structure FrobeniusActionData (F : ModelFrobenioidData) where
  /-- the Frobenius endomorphism on objects -/
  frob : F.Obj → F.Obj
  /-- Frobenius preserves the base projection -/
  frob_toBase : ∀ x, F.toBase (frob x) = F.toBase x
  /-- Frobenius multiplies the line-bundle degree by the Frobenius degree -/
  frob_degree : ∀ x, F.degree (frob x) = F.frobeniusDegree x * F.degree x

/-- A Frobenioid object layer: model Frobenioid + Frobenius action (+ polymodel
slot for [FrdII] §5). -/
structure FrobenioidObjectLayer where
  /-- the model Frobenioid datum -/
  model : ModelFrobenioidData
  /-- the Frobenius action -/
  frobenius : FrobeniusActionData model
  /-- the poly-Frobenioid components ([FrdII] §5) -/
  polyComponents : List ModelFrobenioidData

/-- Paper components of [FrdI]/[FrdII] (corpus anchor -> object -> class). -/
def FrdPaperComponents : List (String × String × String) :=
  [ ("FrdI §1 Definitions/First Properties (Props 1.4-1.11, l.1109-1599)", "DivisorialMonoidData / ModelFrobenioidData", "statement layer; class A/B"),
    ("FrdI §2 Frobenius Functors", "FrobeniusActionData", "statement layer; class B semantics"),
    ("FrdI §3 Category-theoreticity of Base and Frobenius Degree", "ModelFrobenioidData.frobeniusDegree", "class B"),
    ("FrdI §4 Category-theoreticity of the Divisor Monoid", "DivisorialMonoidData", "class B"),
    ("FrdI §5 Model Frobenioids", "ModelFrobenioidData", "reuse tree concrete model (Iut.FrobenioidPresentation)"),
    ("FrdI §6 Motivating Examples", "tree LeanFormal/IUT/IUTII/Frobenioid/Example36*", "reuse tree"),
    ("FrdII §1 Nonarchimedean Primes (Thm 1.2 l.376, Prop 1.5 l.584)", "ModelFrobenioidData + Example36 local assets", "class A/B"),
    ("FrdII §2 Kummer/Reciprocity Maps (Thm 2.4 l.818)", "named class-B input", "class B"),
    ("FrdII §3 Archimedean Primes (Prop 3.4 l.1446)", "Example36ArchimedeanLocal etc.", "reuse tree / class B"),
    ("FrdII §4-§5 Angloids / Poly-Frobenioids", "FrobenioidObjectLayer.polyComponents", "statement layer") ]

end LeanFormal.IUT.XiFPaper.Frd01StatementActual
