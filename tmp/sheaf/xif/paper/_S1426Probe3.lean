import Mathlib.Algebra.Module.Basic

universe u v

structure D (V : Type v) where
  x : V

structure N (V : Type v) (M : Type u) [AddCommMonoid M] [Module ℚ M] where
  local : D.{u, v} V
  action : local.x → M ≃ₗ[ℚ] M
  action_one : ∀ value, action 1 value = value

#check N
