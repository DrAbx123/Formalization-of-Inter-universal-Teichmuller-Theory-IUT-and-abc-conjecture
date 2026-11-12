# S2054: Paper O completion-level carrier gap

Date: 2026-11-02. Layer O. Scope: actual PaperO components, no reduced/stub/Q_p
model substitution.

## Built / proved actual

- S2053PaperORootStackAlignment.lean (EXIT=0):
  component (d) is exactly the multiradial S2040RootStackThetaPilotObject:
  S2053ComponentD_available, S2053ComponentD_root_pow
  (root^(2l)=qVAlgClosedUnit), S2053ComponentD_theta_value
  (theta action values = lgpThetaValue).
  Axioms: [propext, Classical.choice, Quot.sound].
  Source SHA256 7c458b1a00df21cad0c5b004cd568d7bd0771cd91e2d5c2a9bdcbf024a117efe.
  olean SHA256 1d6674bcdb976ea2faece5668d2ff6b5215ec4e7afec6f471571bda9468e9daf.

## S2035 repair attempt: blocked

S2035ActualOUnitsMuActual source SHA256
4c52091defbacc330c5f7dee34bc381a9b1e26b9f13d447f2673341b903a29b7.
Current state: EXIT=1; axioms show sorryAx in GvEquiv and unitsEquiv_action.

Concrete errors:
- galoisConj/galoisConjSymm: AlgEquiv field unification failures
  (left_inv/right_inv goals are not closed by RingEquiv/AlgEquiv simp);
- commutes' goals require equivOfEquiv_algebraMap on both sides;
- heartbeat timeouts during galoisConjSymm/GvEquiv abstraction.

## Deeper obstruction (more important than the proof errors)

S2035 defines

  OUnitsActual v := (Lv v)^x,

i.e. **all units of the algebraic closure**, not the units of its valuation
ring. The paper's local O^× is the group of units of the integral ring
Integers (Lv v) (equivalently norm exactly 1), which is S1978's carrier
(Integers (AlgebraicClosure Q_p))^x. The all-units group contains elements of
norm != 1, so it cannot be the paper local O^×. Therefore repairing section 3
alone would not make S2035 the completion-level paper O^× carrier.

Exact first missing for the completion carrier:
1. actual completion QPlace integral-units carrier
   (Integers (SourceAlgebraicClosure (QPlace v)))^x, plus its mu quotient;
2. a norm/isometry identification with the Q_p model S1978 local units; the
   existing algClosureEquiv is only a ring equivalence and does not preserve
   the integer subring/norm, so it cannot identify O^× by itself;
3. S1978RebasedPaperInput D with its rebased paper q-pilot object.

## Other component gaps

(a) S2037FirstMissing D = Nonempty (CurvePi1Family ...): no actual geometric
    pi_1 family. Source SHA256
    24c2599382041ae7bf6aa4ac9125c73b4234266ec38f29869a8a71a1b63f17ad.
(b) S2031: Fmod-indexed actual theta/Gaussian monoid family missing; only
    one-column models. Source SHA256
    b451d785412d034400349e7f431488e402d758c55e28abfd3a5537b15b6b818f.
(e) S2045/S2046: actual local carrier/evaluation components, but paper
    attachment remains S1895AttachmentMissing.
    S2045 SHA256 0eadda7af9d0414500aa65bddaa9fc5f88b788aea14b1e2d1e5805e8f485e176;
    S2046 SHA256 b96e8593807ee20b80409ed69564564ba39fff1ea7139060ac5c26f5500155ec.

No reduced/stub/Q_p model is claimed as PaperO. No fake/sorry in S2053.
