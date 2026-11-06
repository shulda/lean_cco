import CCO.TypedOrbitFrames.ActualPairwiseHelly
import CCO.ExactCRT.FiniteOrder

/-!
# B053 C29: proper meet-irreducible J forces one actual old coordinate

For a finite family of FULL actual old invariant equivalences E_i
the kernel H is their literal old relation intersection. Whenever
H <= J and J is a proper FULL original meet-irreducible,
original semantic CCO + FULL NR2 give distributivity of the
FULL invariant lattice, and the accepted B008 finite meet-prime
lemma forces at least one E_i <= J.

The nonempty finite family is not silently assumed: when it
is empty H is old Top, so the premise H <= J contradicts
the properness of J. This covers source11's empty branch
without introducing a nullary hidden coordinate.

The forced J-quotient value of every real point in the joint
fibre is therefore determined by the SAME existing E_i-class.
This claims no new named-quotient function: terminal MI
name restriction and actual upward maps remain separate.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original
open CCO.ExactCRT.FiniteOrder
open CCO.RealClosure.Bounds

universe u v w t
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}

/-- Exact decomposition of the old FULL finite meet into its
first old source kernel and the meet of remaining kernels.
The proof uses the actual old relation semantics, not
any assumed distributive law. -/
theorem original_actual_meet_equivalence_cons
    {n : Nat} (E : Fin (n+1) → ColourEq S i) :
    originalActualMeetEquivalence S E =
      E 0 ⊓ originalActualMeetEquivalence S (fun j : Fin n => E j.succ) := by
  apply ColourEq.ext S i
  intro x y
  change (∀ j : Fin (n+1), E j x y) ↔
    E 0 x y ∧ ∀ j : Fin n, E j.succ x y
  constructor
  · intro h
    exact ⟨h 0, fun j => h j.succ⟩
  · rintro ⟨hzero,hrest⟩ j
    cases j using Fin.cases with
    | zero => exact hzero
    | succ j => exact hrest j

/-- General finite-meet selection with an explicitly supplied
binary meet-prime rule and proper target. The terminal source
instance below derives this rule from the genuine B008 exact
distributivity; it is NOT assumed as new source input there. -/
theorem original_actual_meet_select_of_prime
    (J : ColourEq S i)
    (hJproper : J ≠ ⊤)
    (hPrime : ∀ A B : ColourEq S i,
      A ⊓ B ≤ J → A ≤ J ∨ B ≤ J) :
    ∀ {m : Nat} (E : Fin m → ColourEq S i),
      originalActualMeetEquivalence S E ≤ J →
      ∃ j : Fin m, E j ≤ J := by
  intro m
  induction m with
  | zero =>
      intro E h
      have hTop : (⊤ : ColourEq S i) ≤ J := by
        rw [← original_actual_empty_meet_is_top S E]
        exact h
      exact False.elim (hJproper (le_antisymm le_top hTop))
  | succ n ih =>
      intro E h
      let tail : Fin n → ColourEq S i := fun j => E j.succ
      have hs : E 0 ⊓ originalActualMeetEquivalence S tail ≤ J := by
        rw [← original_actual_meet_equivalence_cons S E]
        exact h
      rcases hPrime (E 0) (originalActualMeetEquivalence S tail) hs with h0 | ht
      · exact ⟨0,h0⟩
      · obtain ⟨j,hj⟩ := ih tail ht
        exact ⟨j.succ,hj⟩

/-- Source-specific C29 finite meet-primality in the genuine
FULL invariant original lattice. The hypotheses are exactly
original homogeneity, old semantic HOM CCO, FULL NR2 and a
proper meet-irreducible J; no hidden SAP or new axiom. -/
theorem original_terminal_full_meet_prime_coordinate
    {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : SortNR2 S i)
    (J : ColourEq S i)
    (hJproper : J ≠ ⊤)
    (hMI : BinaryMeetIrreducible J)
    {m : Nat} (E : Fin m → ColourEq S i)
    (hHE : originalActualMeetEquivalence S E ≤ J) :
    ∃ j : Fin m, E j ≤ J := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H
  letI : DistribLattice (ColourEq S i) :=
    terminalDistribLattice S H cco nr2
  have hPrime : ∀ A B : ColourEq S i,
      A ⊓ B ≤ J → A ≤ J ∨ B ≤ J := by
    intro A B hh
    exact binary_meet_irreducible_prime hMI hh
  exact original_actual_meet_select_of_prime S
    J hJproper hPrime E hHE

/-- One of the existing original E_i-coordinates DETERMINES
the actual J-class throughout the complete common real fibre,
provided literal full-terminal meet-primality applies.
The named quotient-language factorization is not invented. -/
theorem original_terminal_common_fibre_forced_J
    {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : SortNR2 S i)
    {m : Nat}
    (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (J : ColourEq S i)
    (hJproper : J ≠ ⊤)
    (hMI : BinaryMeetIrreducible J)
    (hHE : originalActualMeetEquivalence S E ≤ J) :
    ∃ j : Fin m, E j ≤ J ∧
      ∀ x y : X i,
        x ∈ originalActualClassFibre S E c →
        y ∈ originalActualClassFibre S E c → J x y := by
  obtain ⟨j,hEj⟩ :=
    original_terminal_full_meet_prime_coordinate
      S H cco nr2 J hJproper hMI E hHE
  exact ⟨j,hEj,
    fun x y hx hy =>
      original_actual_fibre_forced_coordinate
        S E c J j hEj hx hy⟩

end CCO.TypedOrbitFrames
