structure Foo where
  pt : Type

structure Bar (A B : Type) (f : A → B) where
  val : A

def API (A B : Type) (i : A → B) : Prop :=
  ∃ (D : Foo) (h : D.pt = B) (F : Bar A D.pt (h.symm ▸ i)), True

example (A B : Type) (i : A → B) (h : API A B i) : True := by
  rcases h with ⟨D, hpt, F, _⟩
  cases hpt
  have : Bar A B i := F
  trivial
