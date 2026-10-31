import CCO.TerminalLattice.PositiveBranchCycles

/-!
# B050 C27/C30: ordered actual old endpoints for closed positive branch words

The C30 positive-word closure theorems previously produced a CLOSED
RAW concatenation only. We expose the complete finite chain of
INTERMEDIATE ORIGINAL-SORT marked-root values, in the exact order of the
positive typed branches. Each whole branch relation may use other old
named sorts internally; their real walks remain supplied by accepted
B002 when the marked cycle is reconstructed.

The chain is a genuine recursive existential predicate, not a new
cycle-realization oracle or a substitute for source CCO. An actual
compression/rotation-to-marked-projection bridge is still required to
index these values by the literal B002 marked vertices and realize
every used original edge of each cycle.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- An actual finite old path of the listed WHOLE positive typed branches,
with one original-sort intermediate point between each consecutive pair.
The empty list is genuine equality of path endpoints, not a positive
atomic word or a fictional STRONG identity menu. -/
def originalPositiveBranchChain {i : ι} :
    List (PositiveWord S i i) → X i → X i → Prop
  | [], x, y => x = y
  | word :: rest, x, y =>
      ∃ z : X i,
        PositiveWord.represented S word x z ∧
        originalPositiveBranchChain rest z y

/-- An ordered list of true OLD branch relations is equivalent to the
represented relation of the corresponding real left-associated positive
word concatenation. This preserves the exact order and every boundary
root; it does not commute or reverse any internal OLD atomic letters. -/
theorem originalPositiveBranchPath_represented_iff_chain
    {i : ι} (first : PositiveWord S i i)
    (remaining : List (PositiveWord S i i))
    (x y : X i) :
    PositiveWord.represented S
      (originalPositiveBranchPath S first remaining) x y ↔
      originalPositiveBranchChain S (first :: remaining) x y := by
  induction remaining generalizing first x y with
  | nil =>
      change PositiveWord.represented S first x y ↔
        (∃ z : X i, PositiveWord.represented S first x z ∧ z = y)
      constructor
      · intro h
        exact ⟨y,h,rfl⟩
      · rintro ⟨z,h,rfl⟩
        exact h
  | cons word rest ih =>
      change PositiveWord.represented S
          (originalPositiveBranchPath S (PositiveWord.append S first word) rest) x y ↔
        (∃ z : X i, PositiveWord.represented S first x z ∧
          ∃ t : X i, PositiveWord.represented S word z t ∧
            originalPositiveBranchChain S rest t y)
      rw [ih (PositiveWord.append S first word) x y]
      change (∃ t : X i,
          PositiveWord.represented S (PositiveWord.append S first word) x t ∧
          originalPositiveBranchChain S rest t y) ↔
        (∃ z : X i, PositiveWord.represented S first x z ∧
          ∃ t : X i, PositiveWord.represented S word z t ∧
            originalPositiveBranchChain S rest t y)
      rw [PositiveWord.represented_append S first word]
      change (∃ t : X i,
          (∃ z : X i, PositiveWord.represented S first x z ∧
            PositiveWord.represented S word z t) ∧
          originalPositiveBranchChain S rest t y) ↔
        (∃ z : X i, PositiveWord.represented S first x z ∧
          ∃ t : X i, PositiveWord.represented S word z t ∧
            originalPositiveBranchChain S rest t y)
      constructor
      · rintro ⟨t,⟨z,hFirst,hWord⟩,hRest⟩
        exact ⟨z,hFirst,t,hWord,hRest⟩
      · rintro ⟨z,hFirst,t,hWord,hRest⟩
        exact ⟨t,⟨z,hFirst,hWord⟩,hRest⟩

/-- SOURCE C30, the actual labelled saturated complementary branch
path plus closing branch gives explicit real old endpoint values
for EVERY ordered complementary branch, sharing both endpoints with
the original closing word. This strengthens the previous single-loop
RAW conclusion without adding SAP, CCO or an unproved provider.

No arbitrary marked-vertex indexing is assumed here. -/
theorem original_saturated_positive_path_branch_values
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ParityHasse.Original.ColourEq S i)
    (first : PositiveWord S i i)
    (remaining : List (PositiveWord S i i))
    (closing : PositiveWord S i i)
    (D : S.Menu i i)
    (hD : D.Nonempty)
    (hDinside : D ⊆
      originalEquivDiversityPalette S K)
    (hClosing : D ⊆ PositiveWord.profile S closing)
    (hPath : originalPositiveStrongPath S
        ((first :: remaining).map (PositiveWord.profile S)) =
      some (originalEquivDiversityPalette S K)) :
    ∃ x y : X i,
      originalPositiveBranchChain S (first :: remaining) x y ∧
      PositiveWord.represented S closing x y := by
  obtain ⟨x, hx⟩ :=
    original_saturated_positive_path_closes_with_branch
      S H sap K first remaining closing D
      hD hDinside hClosing hPath
  rw [RawWord.relation_append S, RawWord.relation_reverse S,
    ← PositiveWord.represented_toRawWord S
      (originalPositiveBranchPath S first remaining),
    ← PositiveWord.represented_toRawWord S closing] at hx
  change (∃ y : X i,
      PositiveWord.represented S
        (originalPositiveBranchPath S first remaining) x y ∧
      PositiveWord.represented S closing x y) at hx
  obtain ⟨y,hChain,hClose⟩ := hx
  exact ⟨x,y,
    (originalPositiveBranchPath_represented_iff_chain
      S first remaining x y).mp hChain,hClose⟩

/-- SOURCE C30 centre-star: the actual K-diversity spoke, followed by
the ORIGINAL ordered list of graph branches, has a real endpoint at
each root; another genuine positive spoke connects the same two final
endpoints. This does not yet assert that the ordered list was obtained
from the specific marked cycle of the actual sparse network. -/
theorem original_centre_spokes_positive_branch_values
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spoke : PositiveWord S i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (pathWords : List (PositiveWord S i i))
    (hPath : ∀ P ∈ pathWords,
      (PositiveWord.profile S P).Nonempty ∧
      PositiveWord.profile S P ⊆
        originalEquivDiversityPalette S K) :
    ∃ x y : X i,
      originalPositiveBranchChain S (spoke :: pathWords) x y ∧
      PositiveWord.represented S spoke x y := by
  obtain ⟨x,hClosed⟩ :=
    original_centre_spokes_positive_word_cycle
      S H sap K hK spoke hSpoke pathWords hPath
  rw [RawWord.relation_append S, RawWord.relation_reverse S,
    ← PositiveWord.represented_toRawWord S
      (originalPositiveBranchPath S spoke pathWords),
    ← PositiveWord.represented_toRawWord S spoke] at hClosed
  change (∃ y : X i,
      PositiveWord.represented S
        (originalPositiveBranchPath S spoke pathWords) x y ∧
      PositiveWord.represented S spoke x y) at hClosed
  obtain ⟨y,hChain,hClosing⟩ := hClosed
  exact ⟨x,y,
    (originalPositiveBranchPath_represented_iff_chain
      S spoke pathWords x y).mp hChain,hClosing⟩

end CCO.TerminalLattice
