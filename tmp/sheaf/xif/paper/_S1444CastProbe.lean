structure Wrap (n : Nat) where
  val : Nat

-- standard direction
def fwd {a b : Nat} (h : a = b) (x : Wrap a) : Wrap b := h ▸ x
-- reverse direction (does the notation flip?)
def rev {a b : Nat} (h : a = b) (x : Wrap a) : Wrap b := h.symm ▸ x
-- cast preserves the field
theorem fwd_val {a b : Nat} (h : a = b) (x : Wrap a) : (fwd h x).val = x.val := by
  cases h
  rfl
theorem rev_val {a b : Nat} (h : a = b) (x : Wrap a) : (rev h x).val = x.val := by
  cases h
  rfl
-- are the two elaborate to the same term?
theorem fwd_eq_rev {a b : Nat} (h : a = b) (x : Wrap a) : fwd h x = rev h x := rfl
