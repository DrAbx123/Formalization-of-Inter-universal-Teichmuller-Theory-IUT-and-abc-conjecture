# S1505: rational tensor base-change equivalence — exact obstruction

Date: 2026-10-31. No Lean file: the requested equivalence is mathematically false.

## 1. Why the proposed equivalence cannot exist

Let M_i = CommonPrimeCompletion (t i).  Each M_i is a finite-dimensional
Q_p-vector space (a local field), and S1474 proves

  IQSpan(sourceDatum_i) = top,

so the rational tensor used in S1474 is

  RatT = tensor over Q of M_i

as a Q-vector space, with every M_i considered as a Q-vector space.

Each M_i has infinite dimension over Q: it is finite-dimensional over Q_p,
and Q_p itself is infinite-dimensional over Q.  Hence RatT is an
infinite-dimensional Q-vector space.

Base change RatT tensor[Q] Q_p has Q_p-dimension equal to dim_Q RatT, which is
infinite.

On the other hand

  SourceBlk j t = tensor over Q_p of M_i

is finite-dimensional over Q_p, with dimension product of the finite
dimensions [M_i : Q_p].

Therefore there is no Q_p-linear equivalence

  RatT tensor[Q] Q_p  ~=  SourceBlk j t.

No construction preserving all factors can produce one; this is not a missing
lemma about tensor associativity, it is a dimension obstruction.

## 2. Exact first obstruction

The first false assertion is the dimension equality that a base-change
equivalence would imply:

  Module.finrank Q_p (RatT tensor[Q] Q_p) = Module.finrank Q_p (SourceBlk j t).

The left side is dim_Q RatT (infinite); the right side is finite.  Equivalently,
the natural comparison map from the base change to SourceBlk has an infinite-
dimensional kernel and cannot be injective.

## 3. What is actually a valid comparison

The valid comparison is not an equivalence but a canonical Q_p-linear map

  RatT tensor[Q] Q_p  ->  SourceBlk j t

induced by pure tensors, or a map after replacing the rational tensor by a
finite integral/rational lattice of the correct rank.  Such a comparison is
surjective in the pure-tensor span but is not injective, precisely because
RatT is a Q-vector space with Q_p-relations not imposed.

The paper-level comparison must therefore be stated at the integral lattice
level (integralLogShellLattice, finite free over Z_p) or with an explicit
kernel/quotient, not as an equivalence of the full rational IQSpan tensor with
the Q_p tensor.

## 4. Conclusion

- The requested base-change equivalence is impossible for the S1474 objects.
- Exact first obstruction: infinite Q_p-dimension of RatT tensor[Q] Q_p versus
  finite Q_p-dimension of SourceBlk j t.
- A correct comparison is a surjective canonical map or a lattice-level
  comparison, with the kernel/quotient made explicit.
- No Lean file written to avoid encoding a false equivalence; report EXIT=0.
