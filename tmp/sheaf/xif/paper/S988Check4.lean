structure Foo where
  [inst : Inhabited Nat]
  x : Nat
noncomputable def f : Foo := { inst := inferInstance, x := 0 }
