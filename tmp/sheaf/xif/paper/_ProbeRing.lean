import Mathlib
example (M s : Real) : (3*M+3*M^2+M^3)*s =
    M*s + M*s + M*s + (M^2*(s*s)+M^2*(s*s)+M^2*(s*s)) + M^3*(s*s*s) := by
  ring
