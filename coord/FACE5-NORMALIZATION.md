# FACE5-NORMALIZATION — tame term and (2p)^-1 factor (A911)

Status: source-level normalization audit. Not an IUT theorem.

## 1. Where (2p)^-1 lives

`Iut/Concrete/LocalConstruct/LocalLogShell.lean:39-41`:
    def logShell : Set k :=
      {y | exists u, ||u-1|| < 1 and y = (2 * (p : k))^-1 * padicLog u}.

So the (2p)^-1 factor is ALREADY inside the log-shell used by
`Iut/WallEquiv/VcI.lean:464 logShellRadius` (it sSup's -ord over `Iut.logShell`).
It is therefore already included in `hullPacket_finite` and `hullPacket_tame`;
no separate -log(2p) term is allowed.

## 2. Tame e=1 term is exactly 0, not an artefact

For unramified odd p (e=1, the relevant conditions hold),
`LocalLogShell.lean:101-107` (`logShell_eq_integer`) proves
    logShell k p = (integer ring of k)   as a set.
Thus the normalized component volume of the log-shell relative to the integral
is 0; the lana tame theorem `hullPacket_tame` (VcI.lean:844)
    hullPacket i (finite p) = sum_c w_c * sum_j (1 - 1/e_cj) * log p
at e_cj = 1 gives 0 exactly.  There is NO extra -log(2p).

(If the (2p)^-1 factor were missing, one would get an extra -log(2p); the source
shows it is present, so that correction does not apply.)

## 3. Relation to paperB exponent

`padicValNat_sub_div_le_logShellPaperBExponent` concerns the different/shell
upper-bound exponent B, not the radius normalization.  paperB is an upper bound
on normalized different, and does not add a -log(2p) to the hull term.  At tame
e=1, radius=0 is consistent with paperB: no contradiction.

## 4. Consequence for Face5

- tame p=11 with e=1: hullPacket_p = 0 is CORRECT; per-place target
  `hullPacket_p - (sF-1)A_p = -(sF-1)A_p < 0` is real, not a normalization artefact.
- Therefore an all-tame section cannot make `V - (sF-1)A >= 0`; the face5
  section construction MUST use wild places (e >= 2, 1-1/e > 0) or arch.
- Updated tame formula (no extra log term):
    hullPacket_tame = sum_c w_c * sum_j (1 - 1/e_cj) * log p,
  with e_cj=1 => 0.
- stepxi should search weights on wild/arch places; all-tame is recorded as an
  OBSTACLE (negative contribution), not a candidate.
