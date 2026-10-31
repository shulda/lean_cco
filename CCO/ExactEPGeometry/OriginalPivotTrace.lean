import CCO.ExactEPGeometry.PrefixExactLargestLift
import CCO.ParityHasse.Original.ParitySeed
import CCO.ParityHasse.Original.GraphBipartite

/-!
# B062 C38–C40: a current odd pivot detects original orbital bipartiteness

All finite source powers are actual equality-inclusive RAW represented
relations, including length ZERO as genuine Id. The C28 full-character
trace-product certificate identifies an old power on a current parent
with the power of the literal original atomic trace, provided the
current trace is nonempty. Current homogeneity makes that trace serial.

Consequently, an ACTUAL nonempty bipartite current atom trace forces
the ORIGINAL atom to have no odd closed walks; all even, odd and
connectivity profiles then restrict literally, including the genuine
diagonal. The original parity seed and nonempty RAW exact parity
profiles come from the accepted original source, not a new axiom.

The hypotheses deliberately include a real current nonempty pivot
and an actual current no-odd-walk certificate. Connecting these to
the selected stage's actual gate is a separate C41–C43 obligation.
-/

universe u v w t

namespace CCO.ExactEPGeometry.OriginalPivotTrace

open APCharacter.Towers
open CCO.ExactEPGeometry
open CCO.RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (tp : ExactTraceProduct A.source B.source P)
variable {p : B.Sorts}

/-- Literal old relation on the actual named CURRENT parent. The
points are real B.Point elements, not nominal colours or quotient
representatives. -/
def currentTrace
    (R : A.Point (P.parent p) → A.Point (P.parent p) → Prop) :
    B.Point p → B.Point p → Prop :=
  fun x y => R (P.point p x) (P.point p y)

/-- True RAW exactness of every power INCLUDING exponent zero.
The zero power is logical identity, not an extra diversity colour. -/
theorem relPow_fullExact
    (R : A.Point (P.parent p) → A.Point (P.parent p) → Prop)
    (hExact : FullExact A.source R) (n : Nat) :
    FullExact A.source (relPow R n) := by
  induction n with
  | zero =>
      exact fullExact_identity A.source (P.parent p)
  | succ n ih =>
      exact (exactCalculus_of_homogeneous_CCO
        A.source A.homogeneous A.cco).comp hExact ih

/-- Every original power is the ACTUAL typed current power under
the full (TP) certificate. Both input traces are genuinely nonempty:
a current serial first edge and a current serial n-step suffix.
No arbitrary middle sort can replace the displayed sort p. -/
include tp in
theorem relPow_current_iff
    (R : A.Point (P.parent p) → A.Point (P.parent p) → Prop)
    (hExact : FullExact A.source R)
    (hSerial : ∀ x : B.Point p, ∃ y : B.Point p,
      currentTrace A B P R x y)
    (n : Nat) :
    ∀ x y : B.Point p,
      relPow R n (P.point p x) (P.point p y) ↔
        relPow (currentTrace A B P R) n x y := by
  let Rcur := currentTrace A B P R
  have hSerialPower : ∀ n : Nat, ∀ x : B.Point p,
      ∃ y : B.Point p, relPow Rcur n x y := by
    intro k
    induction k with
    | zero =>
        intro x
        exact ⟨x,rfl⟩
    | succ k ih =>
        intro x
        obtain ⟨y,hxy⟩ := hSerial x
        obtain ⟨z,hyz⟩ := ih y
        exact ⟨z,y,hxy,hyz⟩
  induction n with
  | zero =>
      intro x y
      exact ProjectedWords.point_eq_iff A.source B.source P x y
  | succ n ih =>
      intro x z
      have hPowerExact := relPow_fullExact A B P R hExact n
      obtain ⟨D,hD⟩ := hExact
      obtain ⟨E,hE⟩ := hPowerExact
      let x₀ : B.Point p := Classical.choice (B.source.nonemptySort p)
      have hInputD :
          ∃ a b : B.Point p,
            RawExact.evaluate A.source D.words
              (P.point p a) (P.point p b) := by
        obtain ⟨y,hxy⟩ := hSerial x₀
        refine ⟨x₀,y,?_⟩
        rw [hD]
        exact hxy
      have hInputE :
          ∃ a b : B.Point p,
            RawExact.evaluate A.source E.words
              (P.point p a) (P.point p b) := by
        obtain ⟨y,hxy⟩ := hSerialPower n x₀
        refine ⟨x₀,y,?_⟩
        rw [hE]
        exact (ih x₀ y).mpr hxy
      have hTP := tp.product D E hInputD hInputE x z
      rw [hD,hE] at hTP
      change (∃ m : B.Point p,
          Rcur x m ∧ relPow R n (P.point p m) (P.point p z)) ↔
        relPow R (n+1) (P.point p x) (P.point p z) at hTP
      change relPow R (n+1) (P.point p x) (P.point p z) ↔
        ∃ m : B.Point p, Rcur x m ∧ relPow Rcur n m z
      constructor
      · intro hOld
        obtain ⟨m,hm,hNext⟩ := hTP.mpr hOld
        exact ⟨m,hm,(ih m z).mp hNext⟩
      · rintro ⟨m,hm,hNext⟩
        exact hTP.mp ⟨m,hm,(ih m z).mpr hNext⟩

/-- All even-length current walks, with true zero-length identity,
are exactly the old even-walk equivalence restricted to p. -/
include tp in
theorem evenWalk_current_iff
    (R : A.Point (P.parent p) → A.Point (P.parent p) → Prop)
    (hExact : FullExact A.source R)
    (hSerial : ∀ x : B.Point p, ∃ y : B.Point p,
      currentTrace A B P R x y)
    (x y : B.Point p) :
    EvenWalk R (P.point p x) (P.point p y) ↔
      EvenWalk (currentTrace A B P R) x y := by
  constructor
  · rintro ⟨n,hn,hxy⟩
    exact ⟨n,hn,(relPow_current_iff A B P tp R hExact hSerial n x y).mp hxy⟩
  · rintro ⟨n,hn,hxy⟩
    exact ⟨n,hn,(relPow_current_iff A B P tp R hExact hSerial n x y).mpr hxy⟩

/-- Original odd RAW profile has the SAME trace as the odd current
profile. Nonempty input traces are retained at every TP induction. -/
include tp in
theorem oddWalk_current_iff
    (R : A.Point (P.parent p) → A.Point (P.parent p) → Prop)
    (hExact : FullExact A.source R)
    (hSerial : ∀ x : B.Point p, ∃ y : B.Point p,
      currentTrace A B P R x y)
    (x y : B.Point p) :
    OddWalk R (P.point p x) (P.point p y) ↔
      OddWalk (currentTrace A B P R) x y := by
  constructor
  · rintro ⟨n,hn,hxy⟩
    exact ⟨n,hn,(relPow_current_iff A B P tp R hExact hSerial n x y).mp hxy⟩
  · rintro ⟨n,hn,hxy⟩
    exact ⟨n,hn,(relPow_current_iff A B P tp R hExact hSerial n x y).mpr hxy⟩

/-- The full connected component relation (not necessarily exact)
also restricts precisely; this is the X-part of source E4. -/
include tp in
theorem connectedWalk_current_iff
    (R : A.Point (P.parent p) → A.Point (P.parent p) → Prop)
    (hExact : FullExact A.source R)
    (hSerial : ∀ x : B.Point p, ∃ y : B.Point p,
      currentTrace A B P R x y)
    (x y : B.Point p) :
    ConnectedWalk R (P.point p x) (P.point p y) ↔
      ConnectedWalk (currentTrace A B P R) x y := by
  constructor
  · rintro ⟨n,hxy⟩
    exact ⟨n,(relPow_current_iff A B P tp R hExact hSerial n x y).mp hxy⟩
  · rintro ⟨n,hxy⟩
    exact ⟨n,(relPow_current_iff A B P tp R hExact hSerial n x y).mpr hxy⟩

/-- The current trace of any genuinely named original diversity atom
is invariant under the ACTUAL current homogeneous group. No equivariance
of the two different whole-group actions is assumed. Instead the proved
literal old-colour projection identifies its current colour support. -/
theorem current_atom_invariant
    (c : A.source.Atom (P.parent p) (P.parent p)) :
    TRel.Invariant (G := B.G)
      (currentTrace A B P (A.source.atomRel c)) := by
  intro g x y hxy
  change A.source.colour (P.point p x) (P.point p y) = some c at hxy
  change A.source.colour (P.point p (g • x)) (P.point p (g • y)) = some c
  calc
    _ = Option.map (P.atom p p) (B.source.colour (g • x) (g • y)) :=
      P.colour p p (g • x) (g • y)
    _ = Option.map (P.atom p p) (B.source.colour x y) :=
      congrArg (Option.map (P.atom p p))
        (B.source.colourInvariant_of_homogeneous B.homogeneous g x y)
    _ = A.source.colour (P.point p x) (P.point p y) :=
      (P.colour p p x y).symm
    _ = some c := hxy

/-- A genuinely nonempty ORIGINAL atom trace is serial inside the real
current homogeneous parent p. This is proved, not assumed as an
extra seriality provider. -/
theorem current_atom_serial
    (c : A.source.Atom (P.parent p) (P.parent p))
    (hNE : TRel.Nonempty
      (currentTrace A B P (A.source.atomRel c))) :
    ∀ x : B.Point p, ∃ y : B.Point p,
      currentTrace A B P (A.source.atomRel c) x y :=
  B.source.raw_serial_of_homogeneous B.homogeneous
    (currentTrace A B P (A.source.atomRel c)) hNE
    (current_atom_invariant A B P c)

/-- If the current nonempty trace of a real original diversity atom
has no odd closed walks, the ORIGINAL atom cannot have any odd closed
walk either. Original transitivity carries any old diagonal odd walk to
an actual projected current point; full (TP) reflects it back. -/
include tp in
theorem original_atom_no_odd
    (c : A.source.Atom (P.parent p) (P.parent p))
    (hNE : TRel.Nonempty
      (currentTrace A B P (A.source.atomRel c)))
    (hCurrentNoOdd :
      ∀ x : B.Point p, ∀ n : Nat, Odd n →
        ¬relPow (currentTrace A B P (A.source.atomRel c)) n x x) :
    ∀ a : A.Point (P.parent p), ∀ n : Nat, Odd n →
      ¬relPow (A.source.atomRel c) n a a := by
  let R := A.source.atomRel c
  have hExact : FullExact A.source R :=
    ⟨RawExact.exactDiversityAtom A.source c,
      RawExact.exactDiversityAtom_relation A.source c⟩
  have hSerial :=
    current_atom_serial A B P c hNE
  intro a n hn hClosed
  let x : B.Point p := Classical.choice (B.source.nonemptySort p)
  have hPowerExact : FullExact A.source (relPow R n) :=
    relPow_fullExact A B P R hExact n
  have hInv : TRel.Invariant (G := A.G) (relPow R n) :=
    hPowerExact.invariant A.source A.homogeneous
  have hEvery : ∀ b : A.Point (P.parent p), relPow R n b b :=
    original_invariant_reflexive_of_one A.source A.homogeneous
      (relPow R n) hInv a hClosed
  have hCur : relPow (currentTrace A B P R) n x x :=
    (relPow_current_iff A B P tp R hExact hSerial n x x).mp
      (hEvery (P.point p x))
  exact hCurrentNoOdd x n hn hCur

/-- Source C38: a genuine nonempty bipartite current odd-pivot atom
trace forces the ORIGINAL named atom graph to be bipartite. This uses
the actual old graph and all odd closed walks, not just finite tests. -/
include tp in
theorem original_atom_bipartite
    (c : A.source.Atom (P.parent p) (P.parent p))
    (hNE : TRel.Nonempty
      (currentTrace A B P (A.source.atomRel c)))
    (hCurrentNoOdd :
      ∀ x : B.Point p, ∀ n : Nat, Odd n →
        ¬relPow (currentTrace A B P (A.source.atomRel c)) n x x) :
    (atomGraph A.source c).IsBipartite := by
  have hNo := original_atom_no_odd A B P tp c hNE hCurrentNoOdd
  apply no_odd_closed_walk_isBipartite
  intro a q hOdd
  exact hNo a q.length hOdd
    ((relPow_atom_iff_walk A.source c q.length a a).mpr ⟨q,rfl⟩)

/-- C38–C40 source parity outputs after reflecting genuine current
bipartiteness. The original FULL invariant interval has true relative
index two; the original even/odd RAW exact profiles are real and nonempty.
Original connectivity need not be RAW exact. -/
include tp in
theorem original_atom_parity
    (c : A.source.Atom (P.parent p) (P.parent p))
    (hNE : TRel.Nonempty
      (currentTrace A B P (A.source.atomRel c)))
    (hCurrentNoOdd :
      ∀ x : B.Point p, ∀ n : Nat, Odd n →
        ¬relPow (currentTrace A B P (A.source.atomRel c)) n x x) :
    (atomGraph A.source c).IsBipartite ∧
    (evenColourEq A.source A.homogeneous c ⋖
      connectivityColourEq A.source A.homogeneous c) ∧
    (∀ a : A.Point (P.parent p),
      relativeIndex
        (evenColourEq A.source A.homogeneous c).val
        (connectivityColourEq A.source A.homogeneous c).val a = 2) ∧
    (∃ Y O : RawExact.NonemptyExact A.source (P.parent p) (P.parent p),
      (∀ x y, RawExact.evaluate A.source Y.words x y ↔
        evenColourEq A.source A.homogeneous c x y) ∧
      (∀ x y, RawExact.evaluate A.source O.words x y ↔
        OddWalk (A.source.atomRel c) x y)) := by
  have hNo := original_atom_no_odd A B P tp c hNE hCurrentNoOdd
  exact ⟨original_atom_bipartite A B P tp c hNE hCurrentNoOdd,
    parity_seed_cover A.source A.homogeneous c hNo,
    fun a => parity_seed_index_two A.source A.homogeneous c hNo a,
    parity_profiles_nonempty_exact A.source A.homogeneous c⟩

/-- Literal source equation E4, including the equality-containing
even part and the NON-exact connectivity upper relation. All three
parts use the SAME actual old c and displayed current parent p. -/
include tp in
theorem original_atom_E4
    (c : A.source.Atom (P.parent p) (P.parent p))
    (hNE : TRel.Nonempty
      (currentTrace A B P (A.source.atomRel c))) :
    let R := currentTrace A B P (A.source.atomRel c)
    (∀ x y : B.Point p,
      evenColourEq A.source A.homogeneous c
        (P.point p x) (P.point p y) ↔ EvenWalk R x y) ∧
    (∀ x y : B.Point p,
      OddWalk (A.source.atomRel c) (P.point p x) (P.point p y) ↔
        OddWalk R x y) ∧
    (∀ x y : B.Point p,
      connectivityColourEq A.source A.homogeneous c
        (P.point p x) (P.point p y) ↔ ConnectedWalk R x y) := by
  dsimp only
  have hExact : FullExact A.source (A.source.atomRel c) :=
    ⟨RawExact.exactDiversityAtom A.source c,
      RawExact.exactDiversityAtom_relation A.source c⟩
  have hSerial := current_atom_serial A B P c hNE
  exact ⟨evenWalk_current_iff A B P tp (A.source.atomRel c)
      hExact hSerial,
    oddWalk_current_iff A B P tp (A.source.atomRel c)
      hExact hSerial,
    connectedWalk_current_iff A B P tp (A.source.atomRel c)
      hExact hSerial⟩

end
end CCO.ExactEPGeometry.OriginalPivotTrace
