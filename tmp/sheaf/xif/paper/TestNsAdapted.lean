def Foo (a : ℤ) : Prop := True
namespace Foo
variable (h : Foo 1)
#check h
lemma bar : True := by exact h
end Foo
