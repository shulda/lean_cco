import CCO.TerminalLattice.PositivePathFold

/-!
# B050 C28/C27: a genuine K-diversity spoke saturates any OLD positive path

A centre-containing compressed sparse-star cycle leaves a real K° spoke
among the positive branch factors when one different edge is designated
as closing. Its other factors are nonempty actual OLD same-sort menus
inside the original K-equivalence. This module proves that *one actual*
K° factor suffices to saturate the whole complementary STRONG path,
using genuine original SAP associativity, same-sort commutativity,
and the already proved original K° absorption.

It does NOT claim that a particular projected cycle contains a spoke;
that requires the still-open exact B002 incidence/ordering proof.
No artificial STRONG identity, quotient-reduct action, original CCO,
or source weakening is introduced.
-/

universe u v w t

namespace CCO.TerminalLattice

/-- Move ONE genuinely occurring factor to the start of an arbitrary
finite list, without omitting other occurrences or identifying
repeated factors. The remaining list retains the exact multiplicities. -/
theorem actual_list_perm_cons_of_mem
    {α : Type*} (a : α) (xs : List α) (ha : a ∈ xs) :
    ∃ tail : List α, xs.Perm (a :: tail) := by
  induction xs with
  | nil =>
      simp at ha
  | cons b xs ih =>
      rcases (List.mem_cons).mp ha with hab | hmem
      · subst b
        exact ⟨xs, List.Perm.refl _⟩
      · obtain ⟨tail,hperm⟩ := ih hmem
        refine ⟨b :: tail, ?_⟩
        exact (List.Perm.cons b hperm).trans (List.Perm.swap b a tail).symm

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- Literal SOURCE C28 centre-spoke spectrum for any finite list of
nonempty OLD same-sort STRONG factors lying in K°. If AT LEAST ONE
factor is exactly the genuine original diversity K°, their actual
ordered STRONG path spectrum is K°.

The list may have repeated graph labels; we move WHOLE endpoint menus,
never reorder internal typed old atomic word letters. The optional
`none` denotes zero factors, not a fake STRONG identity relation.
-/
theorem original_K_spoke_occurrence_saturates_path
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i)
    (ds : List (S.Menu i i))
    (hAll : ∀ D ∈ ds,
      D.Nonempty ∧ D ⊆ originalEquivDiversityPalette S K)
    (hSpoke : originalEquivDiversityPalette S K ∈ ds) :
    originalPositiveStrongPath S ds =
      some (originalEquivDiversityPalette S K) := by
  obtain ⟨tail,hPerm⟩ :=
    actual_list_perm_cons_of_mem
      (originalEquivDiversityPalette S K) ds hSpoke
  have hTail : ∀ D ∈ tail,
      D.Nonempty ∧ D ⊆ originalEquivDiversityPalette S K := by
    intro D hD
    apply hAll D
    exact hPerm.symm.subset (List.mem_cons_of_mem _ hD)
  unfold originalPositiveStrongPath
  rw [originalOptionStrongFold_perm S H sap none hPerm]
  change (tail.foldl (originalOptionStrongStep S)
      (some (originalEquivDiversityPalette S K))) =
      some (originalEquivDiversityPalette S K)
  rw [originalOptionStrongFold_some S]
  exact congrArg Option.some
    (originalKSpokePath_absorbed S H sap K tail hTail)

/-- The same conclusion for an ACTUAL list of old positive TYPED
branches. One of their whole STRONG profiles is K°, and all are
nonempty K°-subpalettes. No claim that the selected word itself is
syntactically a spoke is necessary: only its true original profile
matters, so reversal of whole same-sort words is handled separately. -/
theorem original_positive_words_with_K_spoke_saturate
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i)
    (branches : List (PositiveWord S i i))
    (hAll : ∀ word ∈ branches,
      (PositiveWord.profile S word).Nonempty ∧
      PositiveWord.profile S word ⊆ originalEquivDiversityPalette S K)
    (hSpoke : ∃ word ∈ branches,
      PositiveWord.profile S word =
        originalEquivDiversityPalette S K) :
    originalPositiveStrongPath S
      (branches.map (PositiveWord.profile S)) =
      some (originalEquivDiversityPalette S K) := by
  have hMenus : ∀ D ∈ branches.map (PositiveWord.profile S),
      D.Nonempty ∧ D ⊆ originalEquivDiversityPalette S K := by
    intro D hD
    obtain ⟨word,hWord,rfl⟩ := List.mem_map.mp hD
    exact hAll word hWord
  obtain ⟨word,hw,heq⟩ := hSpoke
  have hFull :
      originalEquivDiversityPalette S K ∈
        branches.map (PositiveWord.profile S) := by
    rw [← heq]
    exact List.mem_map.mpr ⟨word,hw,rfl⟩
  exact original_K_spoke_occurrence_saturates_path
    S H sap K (branches.map (PositiveWord.profile S)) hMenus hFull

end CCO.TerminalLattice
