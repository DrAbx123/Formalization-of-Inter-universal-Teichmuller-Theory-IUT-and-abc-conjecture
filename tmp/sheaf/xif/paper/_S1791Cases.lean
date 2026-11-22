structure Foo where
  pt : Type

example (B : Type) (D : Foo) (h : D.pt = B) : B = B := by
  cases h
  rfl

example (B : Type) (D : Foo) (h : D.pt = B) : D.pt = D.pt := by
  cases h
  rfl
