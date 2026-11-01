import CCO.TerminalLattice.OriginalQuotientOrbitalReturn
import CCO.TerminalLattice.FullCoverUniformPowers

/-!
# B050 source09 OWL-P: eventual full quotient powers of ANY external state

At a genuine nonzero FULL original cover J ⋖ K, any nonempty
ORIGINAL-G-invariant quotient relation W inside K/J that contains
one OFF-DIAGONAL quotient pair contains the COMPLETE old-G pair
orbital of that pair. Outside local index two, the latter's
positive RAW quotient powers were already proved to equal K/J
uniformly at every sufficiently large length, including returns.

Monotonicity transfers these same powers to W. This handles
ARBITRARY invariant W, including its genuine QUOTIENT DIAGONAL,
and does not assume that W is a complete orbit, a symmetric
relation, a positive old word, or free of diagonal returns.

This shorter full-source proof uses only the old quotient action,
the accepted C17 full-cover walk theorem and old finite homogeneity.
No CCO, extra SAP, quotient-redacted automorphism group, or
unproved aperiodicity provider.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- Positive quotient walk lengths are monotone in their ACTUAL
binary edge relation, including the zero-length equality case.
The same intermediate quotient classes are retained; no
diversity/identity mixup is possible here. -/
theorem original_relPow_mono
    {Q : Type*} (P W : Q → Q → Prop)
    (hPW : ∀ x y, P x y → W x y) :
    ∀ n x y, relPow P n x y → relPow W n x y := by
  intro n
  induction n with
  | zero =>
      intro x y h
      exact h
  | succ n ih =>
      intro x y h
      obtain ⟨z,hxz,hzy⟩ := h
      exact ⟨z,hPW x z hxz,ih z y hzy⟩

/-- Source09 OWL-P with an ACTUAL external real old pair witnessing
the off-diagonal part of the original-G-invariant quotient state.
No symmetry of W or positivity of its own old-pullback is needed.
-/
theorem original_invariant_quotient_state_uniform_powers_of_external
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ⋖ K)
    (anchor : X i)
    (hNotTwo : relativeIndex J.val K.val anchor ≠ 2)
    (WRel : Quotient J.val → Quotient J.val → Prop)
    (hInvariant : letI : MulAction G (Quotient J.val) :=
        originalQuotientAction S H J
      ∀ g : G, ∀ q r : Quotient J.val,
        WRel q r → WRel (g • q) (g • r))
    (hInside : ∀ q r, WRel q r →
      originalUpperSetoid S J K hJK.le q r)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (hW : WRel (Quotient.mk J.val a) (Quotient.mk J.val b)) :
    ∃ N : Nat, 0 < N ∧
      ∀ n : Nat, N ≤ n →
        ∀ q r : Quotient J.val,
          relPow WRel n q r ↔
            originalUpperSetoid S J K hJK.le q r := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  let P : Quotient J.val → Quotient J.val → Prop :=
    originalQuotientOrbital S (G := G) J a b
  have hLocalIndex :
      relativeIndex J.val K.val a ≠ 2 := by
    intro hTwo
    have hIndex : relativeIndex J.val K.val a =
        relativeIndex J.val K.val anchor :=
      relativeIndex_uniform S H J K a anchor
    exact hNotTwo (hIndex.symm.trans hTwo)
  have hOrbitalInside : ∀ q r, P q r → WRel q r := by
    intro q r hp
    obtain ⟨g,hgq,hgr⟩ := hp
    have hMove := hInvariant g
      (Quotient.mk J.val a) (Quotient.mk J.val b) hW
    have hMoved :
        WRel (Quotient.mk J.val (g • a))
          (Quotient.mk J.val (g • b)) := by
      simpa only [originalQuotient_mk_smul S H J] using hMove
    rw [hgq,hgr] at hMoved
    exact hMoved
  obtain ⟨N,hN,hPower⟩ :=
    originalQuotient_uniform_full_powers
      S H J K hJK a b hab hne hLocalIndex
  refine ⟨N,hN,?_⟩
  intro n hn q r
  constructor
  · intro hWalk
    exact relPow_le_setoid WRel
      (originalUpperSetoid S J K hJK.le)
      hInside n q r hWalk
  · intro hUpper
    exact original_relPow_mono P WRel hOrbitalInside n q r
      ((hPower n hn q r).mpr hUpper)

/-- SOURCE OWL-P for ANY invariant relation state W ⊆ K/J that
contains an ACTUAL off-diagonal pair of J-classes. Crucially, W
may ALSO contain the quotient diagonal, and the conclusion keeps
all quotient diagonal return pairs for every sufficiently high
positive power. No complete-state or off-diagonal-state premise.
-/
theorem original_invariant_quotient_state_uniform_powers
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ⋖ K)
    (anchor : X i)
    (hNotTwo : relativeIndex J.val K.val anchor ≠ 2)
    (WRel : Quotient J.val → Quotient J.val → Prop)
    (hInvariant : letI : MulAction G (Quotient J.val) :=
        originalQuotientAction S H J
      ∀ g : G, ∀ q r : Quotient J.val,
        WRel q r → WRel (g • q) (g • r))
    (hInside : ∀ q r, WRel q r →
      originalUpperSetoid S J K hJK.le q r)
    (hOff : ∃ q r : Quotient J.val,
      q ≠ r ∧ WRel q r) :
    ∃ N : Nat, 0 < N ∧
      ∀ n : Nat, N ≤ n →
        ∀ q r : Quotient J.val,
          relPow WRel n q r ↔
            originalUpperSetoid S J K hJK.le q r := by
  obtain ⟨q,r,hneq,hqr⟩ := hOff
  induction q using Quotient.inductionOn with
  | _ a =>
    induction r using Quotient.inductionOn with
    | _ b =>
      have hne : ¬ J a b := by
        intro h
        exact hneq (Quotient.sound h)
      have hab : K a b :=
        (originalUpperSetoid_mk S J K hJK.le a b).mp
          (hInside _ _ hqr)
      exact original_invariant_quotient_state_uniform_powers_of_external
        S H J K hJK anchor hNotTwo WRel
        hInvariant hInside a b hab hne hqr

end CCO.TerminalLattice
