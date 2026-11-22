universe u v w z
structure Foo {A : Type u} (B : A → Type v) (C : A → Type w) where
  S : A → Type z
#check Foo.{u,v,w,z}
#check Foo (z := z)
