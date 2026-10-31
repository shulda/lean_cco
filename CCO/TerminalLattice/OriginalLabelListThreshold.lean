import CCO.TerminalLattice.PositivePathFold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# B050 C29/C27: original sparse-cycle label pigeonhole in ACTUAL list order

The original private graph-cycle compression produces a truly ORDERED
finite sequence of label occurrences. After choosing a concrete closing
edge, its complementary path already is a list: there is no need to
relabel it as a permutation of a Finset of different formal edge names.

This lemma proves the exact SOURCE threshold r*(N-1) directly for a
finite list of genuine Fin r labels, then consumes the previously proved
original same-sort STRONG grouping/absorption theorem. A separate
B002/W geometry lemma must still identify the ordered concrete list
and prove that its length exceeds this threshold. Neither CCO, SAP on
a quotient, identity colours, nor a new source power premise appear.
-/

namespace CCO.TerminalLattice

open scoped BigOperators

/-- Count every actual label occurrence in a finite list once,
including repetitions. This is the list-order counterpart of
`finiteLabelCount_total`; no distinctness of labels is assumed. -/
theorem original_label_list_count_total {r : Nat} (labels : List (Fin r)) :
    (∑ j : Fin r, labels.count j) = labels.length := by
  classical
  induction labels with
  | nil => simp
  | cons a tail ih =>
      have hOne (j : Fin r) :
          (a :: tail).count j =
            (if j = a then 1 else 0) + tail.count j := by
        by_cases hj : j = a
        · subst j
          simp [List.count_cons, beq_iff_eq, Nat.add_comm]
        · simp [List.count_cons, beq_iff_eq, hj, eq_comm]
      calc
        (∑ j : Fin r, (a :: tail).count j) =
            ∑ j : Fin r, (if j = a then 1 else 0) + tail.count j := by
              apply Finset.sum_congr rfl
              intro j _
              exact hOne j
        _ = (∑ j : Fin r, if j = a then 1 else 0) +
              (∑ j : Fin r, tail.count j) := Finset.sum_add_distrib
        _ = (a :: tail).length := by simp [ih, Nat.add_comm]

/-- Sharp C29 list pigeonhole: if the actual complementary ordered
graph path has strictly more than r*(N-1) edges, one genuine label
occurs at least N times on that SAME list of edges. -/
theorem original_long_label_list_many
    {r N : Nat} (labels : List (Fin r))
    (hLong : r * (N-1) < labels.length) :
    ∃ j : Fin r, N ≤ labels.count j := by
  classical
  by_contra hBad
  have hSmall (j : Fin r) : labels.count j ≤ N-1 := by
    have hn : ¬ N ≤ labels.count j := by
      intro h
      exact hBad ⟨j,h⟩
    omega
  have hSum :
      (∑ j : Fin r, labels.count j) ≤
        ∑ _j : Fin r, (N-1) :=
    Finset.sum_le_sum (fun j _ => hSmall j)
  rw [original_label_list_count_total] at hSum
  simp only [Finset.sum_const, Finset.card_univ,
    Fintype.card_fin] at hSum
  change labels.length ≤ r * (N-1) at hSum
  omega

universe u v w t

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- SOURCE C29 complete original old path saturation directly from
the actual ORDERED list of graph-edge labels. Its length is greater
than r*(N-1), each label's genuine whole original STRONG menu has
literal (N)-fold K° power, and all other real menus are nonempty
subpalettes of K°. Then the true STRONG profile of the whole
complementary path is EXACTLY K°, independent of the order in which
the labels occur. Reordering uses only proven same-sort STRONG
commutativity/associativity, not any typed-word letter permutation.

No graph/girth claim is hidden here: C27 must supply hLong from the
actual accepted B006 sparse cycle and the ONE designated closing edge.
-/
theorem original_long_ordered_label_path_saturates
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i)
    {r N : Nat} (hN : 0 < N)
    (menus : Fin r → S.Menu i i)
    (labels : List (Fin r))
    (hLong : r * (N-1) < labels.length)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K) :
    originalPositiveStrongPath S (labels.map menus) =
      some (originalEquivDiversityPalette S K) := by
  obtain ⟨j,hMany⟩ :=
    original_long_label_list_many labels hLong
  have hNcopy : (N-1)+1 ≤ labels.count j := by omega
  exact original_labelled_strong_path_saturation
    S H sap K menus labels j (N-1) hNcopy
      (hPowers j) hMenus

end CCO.TerminalLattice
