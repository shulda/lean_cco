import CCO.TerminalLattice.FullCoverAlternation
import CCO.TerminalLattice.StrongPaletteBridge
import Mathlib.Algebra.Ring.Parity

/-!
# B050 C19: complete CCO-free original FULL-cover power dichotomy

This is the literal original-atom STRONG palette theorem from the
pinned source, not a quotient RAW or abstract-relation replacement.

Original homogeneous SAP is used to lift genuine quotient walks at
distinct OLD endpoints. The full cover J ⋖ K is in the ORIGINAL
invariant-equivalence lattice, J is genuinely above old identity,
and the complete external T is the full OLD G-quotient orbital
pullback. No semantic CCO, global NR2, distributivity, exactness,
other-sort quotient action, or unproved provider is assumed.

The first alternative covers EVERY positive odd and even exponent,
including 1 and 2. The second alternative covers EVERY exponent
above a single uniform N (including quotient returns).
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- SOURCE C19 `lem:typed-quotient-full-cover-powers`: the exact
old-diversity STRONG powers of ONE complete external full-G quotient
orbital at a FULL original nonzero cover satisfy precisely one
of the two alternatives. In index two, every odd power is T and
every positive even power is Jᵒ. Otherwise every sufficiently long
power equals Kᵒ.

This proves the original same-sort source theorem WITHOUT original
semantic CCO or global NR2. No quotient equality is substituted for
an OLD STRONG identity atom; there is no zero-exponent palette. -/
theorem original_full_cover_strong_power_dichotomy
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (a b : X i) (hab : K a b) (hne : ¬ J a b) :
    (relativeIndex J.val K.val a = 2 ∧
      ∀ n : Nat, 0 < n →
        (Odd n →
          originalStrongPalettePower S
            (originalQuotientOrbitalPalette S (G := G) J a b)
            (n-1) =
          originalQuotientOrbitalPalette S (G := G) J a b) ∧
        (Even n →
          originalStrongPalettePower S
            (originalQuotientOrbitalPalette S (G := G) J a b)
            (n-1) = originalEquivDiversityPalette S J)) ∨
    (relativeIndex J.val K.val a ≠ 2 ∧
      ∃ N : Nat, 0 < N ∧
        ∀ n : Nat, N ≤ n →
          originalStrongPalettePower S
            (originalQuotientOrbitalPalette S (G := G) J a b)
            (n-1) = originalEquivDiversityPalette S K) := by
  by_cases hTwo : relativeIndex J.val K.val a = 2
  · left
    refine ⟨hTwo, ?_⟩
    intro n hn
    constructor
    · intro hnOdd
      obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp hnOdd
      have hIndex : n-1 = 2*k := by omega
      rw [hIndex]
      exact original_index_two_odd_strong_palette
        S H sap J K hJK hJ a b hab hne hTwo k
    · intro hnEven
      obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hnEven
      cases k with
      | zero =>
          omega
      | succ k =>
          have hIndex : n-1 = 2*k+1 := by omega
          rw [hIndex]
          exact original_index_two_even_strong_palette
            S H sap J K hJK hJ a b hab hne hTwo k
  · right
    obtain ⟨N, hN, hPow⟩ :=
      originalQuotient_uniform_strong_palette_powers
        S H sap J K hJK hJ a b hab hne hTwo
    exact ⟨hTwo, N, hN, hPow⟩

end CCO.TerminalLattice
