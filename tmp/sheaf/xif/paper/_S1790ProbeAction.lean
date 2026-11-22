import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.FintypeCat
noncomputable section
open CategoryTheory
example (G : Type) [Group G] : Prop :=
  Nonempty (@CategoryTheory.Equivalence (Action FintypeCat.{0} G) (Action FintypeCat.{0} G) _ _)
