import Mathlib.Tactic

/-! # IUTExternalConfigDefsActual — E1 [Config] configuration-space definitions (class-D layer)

STEP 0 prior-art: deep search 'configuration space|configuration space of|CbGC|
combinatorial reconstruction' -> Mathlib has `Finset`/`Fin`/injective functions (reused,
no need to import algebraic geometry); no LeanFormal configuration-space definition
exists; corpus used for citations.

CORPUS: Mochizuki, 'Topics in Absolute Anabelian Geometry II' ([AbsTopII]) and
'Combinatorial Anabelian Topics' for configuration spaces and combinatorial reconstruction.

LABEL: class-D external-object definitions/statements (proved:=false); no paper result
is claimed. -/

namespace LeanFormal.IUT.XiFPaper.IUTExternalConfigDefsActual

universe u

/-- The ordered configuration space of n labelled points in a type C (the classical
configuration space of n distinct points; [Config]). -/
def ConfigurationSpace (C : Type u) (n : ℕ) : Type u :=
  {f : Fin n → C // Function.Injective f}

/-- The unlabelled configuration space (quotient by permutations), represented as the
image of the ordered configuration space under the symmetric group action: here the
underlying set of `n`-element subsets, encoded as `Finset C` of cardinality n. -/
def UnlabelledConfigurationSpace (C : Type u) (n : ℕ) [DecidableEq C] : Type u :=
  {S : Finset C // S.card = n}

/-- Combinatorial reconstruction statement shape ([CbGC]): the configuration space
determines the anabelioid (as an explicit interface Prop carrying the statement data). -/
def CombinatorialReconstructionStatement (configuration : Type u) (anabelioidData : Type u)
    (reconstructs : configuration → anabelioidData → Prop) : Prop :=
  ∀ c : configuration, ∃ a : anabelioidData, reconstructs c a

/-- Paper-facing statement ledger for [Config]/[CbGC] (class D; no proof). -/
structure IUTExternalConfigRow where
  item : String
  corpus : String
  status : String
  proved : Bool

def iutExternalConfigStatements : List IUTExternalConfigRow :=
  [ ⟨"configuration space of n labelled points", "[Config]", "DEFINITION LAYER (this file)", false⟩,
    ⟨"unlabelled configuration space", "[Config]", "DEFINITION LAYER (this file)", false⟩,
    ⟨"combinatorial reconstruction statement (CbGC)", "[CbGC] §1", "STATEMENT SHAPE (this file), class D", false⟩,
    ⟨"configuration-space reconstruction theorem", "[CbGC] §2", "STATEMENT (class D)", false⟩ ]

theorem iutExternalConfigStatements_length : iutExternalConfigStatements.length = 4 := rfl

#check ConfigurationSpace
#check UnlabelledConfigurationSpace
#check CombinatorialReconstructionStatement
#check iutExternalConfigStatements_length

end LeanFormal.IUT.XiFPaper.IUTExternalConfigDefsActual