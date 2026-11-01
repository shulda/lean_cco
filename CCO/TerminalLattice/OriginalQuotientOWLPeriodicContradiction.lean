import CCO.TerminalLattice.OriginalQuotientOWLFiniteCycle
import CCO.TerminalLattice.OriginalQuotientStatePowers

/-!
# B050 source09 OWL: periodic positive quotient escape contradicts full powers

The finite escape recurrence produces a REAL ORIGINAL-G-invariant
quotient relation R and a genuine nonempty product W of external
complete old-G pair orbitals with R;W=R. The source's CCO-free
full-cover powers force W^n=K/J as soon as W has an actual
off-diagonal quotient pair. Since R is serial and lies in K/J,
R;(K/J)=K/J. Thus R cannot omit any true K/J pair.

This is a pure quotient RELATIONAL argument, not a new semantic
CCO map, and it retains every quotient-diagonal output. The
separate source OWL proof must construct the periodic W from the
finite escape graph and prove its off-diagonal pair; those are
not assumptions of the ultimate external-layer theorem.
-/

universe u v w t

namespace CCO.TerminalLattice

/-- Composing a genuine relation with TRUE equality on its
carrier returns precisely the relation. This is equality of
quotient relations, NOT an invented positive old atom. -/
theorem original_relation_comp_right_eq
    {Q : Type*} (R : Q → Q → Prop) :
    RawSymmetric.compose R Eq = R := by
  funext x y
  apply propext
  constructor
  · rintro ⟨mid,hR,hEq⟩
    subst y
    exact hR
  · intro hR
    exact ⟨y,hR,rfl⟩

/-- If R;W=R, then R;W^n=R for every n, including n=0
where W^0 is the true quotient equality relation. Associativity
is verified on ACTUAL quotient witnesses. -/
theorem original_relation_comp_right_pow_fixed
    {Q : Type*} (R W : Q → Q → Prop)
    (hFixed : R = RawSymmetric.compose R W) :
    ∀ n : Nat, RawSymmetric.compose R (relPow W n) = R := by
  intro n
  induction n with
  | zero =>
      exact original_relation_comp_right_eq R
  | succ n ih =>
      change RawSymmetric.compose R
          (RawSymmetric.compose W (relPow W n)) = R
      calc
        _ = RawSymmetric.compose
              (RawSymmetric.compose R W) (relPow W n) :=
          (original_relation_comp_assoc R W (relPow W n)).symm
        _ = RawSymmetric.compose R (relPow W n) := by
          rw [← hFixed]
        _ = R := ih

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- SOURCE OWL-P contradiction for any REAL periodic
ORIGINAL-G quotient escape state R and nontrivial invariant
label-product W. Both may include TRUE quotient-diagonal pairs.

If R is nonempty and contained in K/J, W is inside K/J and has
an off-diagonal pair, and R;W=R, then R contains ALL of K/J.
Otherwise high full quotient powers of W contradict seriality
of R. The full original cover, original ambient action, and
actual local index!=2 are used exactly in OWL-P, not invented.

This result is available WITHOUT a positive-word assumption on R
or W; those are used in the preceding finite escape construction.
-/
theorem original_periodic_quotient_state_covers_upper
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ⋖ K)
    (anchor : X i)
    (hNotTwo : relativeIndex J.val K.val anchor ≠ 2)
    (R W : OriginalInvariantQuotientState S H J)
    (hRNonempty : ∃ q r : Quotient J.val, R.val q r)
    (hRInside : ∀ q r : Quotient J.val, R.val q r →
      originalUpperSetoid S J K hJK.le q r)
    (hWInside : ∀ q r : Quotient J.val, W.val q r →
      originalUpperSetoid S J K hJK.le q r)
    (hWOff : ∃ q r : Quotient J.val,
      q ≠ r ∧ W.val q r)
    (hFixed : R.val = RawSymmetric.compose R.val W.val) :
    ∀ q r : Quotient J.val,
      originalUpperSetoid S J K hJK.le q r → R.val q r := by
  obtain ⟨N,hN,hPowers⟩ :=
    original_invariant_quotient_state_uniform_powers
      S H J K hJK anchor hNotTwo W.val W.property hWInside hWOff
  have hAllFixed :=
    original_relation_comp_right_pow_fixed
      R.val W.val hFixed N
  have hSerial :=
    originalInvariantQuotientState_serial S H J R hRNonempty
  intro q r hUpper
  obtain ⟨mid,hRmid⟩ := hSerial q
  have hQmid : originalUpperSetoid S J K hJK.le q mid :=
    hRInside q mid hRmid
  have hMidR : originalUpperSetoid S J K hJK.le mid r :=
    (originalUpperSetoid S J K hJK.le).trans
      ((originalUpperSetoid S J K hJK.le).symm hQmid)
      hUpper
  have hWpow : relPow W.val N mid r :=
    (hPowers N le_rfl mid r).mpr hMidR
  have hComposed :
      RawSymmetric.compose R.val (relPow W.val N) q r :=
    ⟨mid,hRmid,hWpow⟩
  rw [hAllFixed] at hComposed
  exact hComposed

end CCO.TerminalLattice
