universe u
variable (C : Type u)
variable (j : Nat)
def foo (j : Nat) : Type := C
#check foo
def bar (j : Nat) : Type := foo C j
#check bar
