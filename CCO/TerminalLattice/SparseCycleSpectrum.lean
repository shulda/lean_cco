import CCO.TerminalLattice.PositivePathFold
import CCO.TerminalLattice.SparseCycleLabels
import Mathlib.Data.Finset.Insert

/-!
# B050 C29: actual old sparse-graph cycles have K-diversity complementary spectra

This bridges the previously verified finite C29 graph-edge label count and
the actual old same-sort STRONG path-product theorem.  The complement of
one chosen graph edge is the genuine FINITE SET of the OTHER graph edges.
The listed edge order is required to be a permutation of exactly that set;
thus no edge may be silently skipped, duplicated or invented.  A later
C27 private-path contraction must produce this particular ordered list
from a typed simple cycle.

No global CCO or new provider is used.  The original K-powers hypothesis
is required explicitly for each complete old-G quotient orbital.
-/

universe u v w t

namespace CCO.TerminalLattice

/-- The number of occurrences of a genuine label in the list of all
finite edges equals the label count in the set of those edges.  This
continues to hold when distinct edges carry identical labels. -/
theorem finiteLabelCount_eq_toList_count
    {α : Type*} [DecidableEq α] {r : Nat}
    (edges : Finset α) (labels : α → Fin r) (target : Fin r) :
    finiteLabelCount edges labels target =
      (edges.toList.map labels).count target := by
  classical
  induction edges using Finset.induction_on with
  | empty =>
      simp [finiteLabelCount]
  | @insert a edges ha ih =>
      have hPerm : ((insert a edges).toList.map labels).Perm
          (labels a :: edges.toList.map labels) :=
        (Finset.toList_insert ha).map labels
      have hCount :
          ((insert a edges).toList.map labels).count target =
            (labels a :: edges.toList.map labels).count target := by
        simpa only [List.count] using
          (hPerm.countP_eq (fun i => i == target))
      calc
        finiteLabelCount (insert a edges) labels target =
            (if labels a = target then 1 else 0) +
              finiteLabelCount edges labels target := by
                simp [finiteLabelCount, Finset.sum_insert ha]
        _ = (labels a :: edges.toList.map labels).count target := by
          simp [ih, List.count_cons, beq_iff_eq, Nat.add_comm]
        _ = ((insert a edges).toList.map labels).count target :=
          hCount.symm

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- C29 genuine complementary graph-cycle path spectrum.

The source girth bound yields a label with AT LEAST N occurrences
after deleting the selected closing edge.  The actual path ordering
contains exactly those edge occurrences, in any order (the permutation
condition exposes the necessary C27 graph-to-word correspondence).
All actual complete old-G external menus have eventual literal strong
powers K-diversity, for N≥1.  Thus their whole complementary STRONG
path, with no zero-length fake identity, has exactly spectrum K-diversity.

This is a strong SAME-SORT endpoint-menu assertion, not a purported
homomorphism of an as-yet unconstructed typed partial diagram. -/
theorem originalSparseGraph_complementary_strong_saturation
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i)
    {q r g N m : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (hGirth : r * (N-1) + 1 ≤ g)
    (hN : 0 < N)
    (hm : 3 ≤ m)
    (vertices : Fin m ↪ Fin W.size)
    (hEdges : ∀ p : Fin m,
      W.graph.Adj (vertices p)
        (vertices (CCO.cyclicNext (by omega : 0 < m) p)))
    (closing : Fin m)
    (menus : Fin r → S.Menu i i)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K)
    (edgeOrder : List (Fin m))
    (hOrder : edgeOrder.Perm
        ((Finset.univ : Finset (Fin m)).erase closing).toList) :
    originalPositiveStrongPath S
      (edgeOrder.map (fun p =>
        menus (W.label s(vertices p,
          vertices (CCO.cyclicNext (by omega : 0 < m) p))))) =
        some (originalEquivDiversityPalette S K) := by
  let labels : Fin m → Fin r :=
    fun p => W.label s(vertices p,
      vertices (CCO.cyclicNext (by omega : 0 < m) p))
  let edges : Finset (Fin m) :=
    (Finset.univ : Finset (Fin m)).erase closing
  obtain ⟨j, hMany⟩ :=
    originalSparseGraph_complementary_label_threshold
      W hGirth hm vertices hEdges closing
  have hEqual :
      finiteLabelCount edges labels j =
        (edges.toList.map labels).count j :=
    finiteLabelCount_eq_toList_count edges labels j
  have hPermMapped : (edgeOrder.map labels).Perm
      (edges.toList.map labels) := hOrder.map labels
  have hSameCount :
      (edgeOrder.map labels).count j =
      (edges.toList.map labels).count j := by
    simpa only [List.count] using
      (hPermMapped.countP_eq (fun k => k == j))
  have hCount : (N-1)+1 ≤ (edgeOrder.map labels).count j := by
    have hMany' : N ≤ finiteLabelCount edges labels j := hMany
    rw [hEqual] at hMany'
    omega
  have hFold :=
    original_labelled_strong_path_saturation
      S H sap K menus (edgeOrder.map labels) j (N-1)
      hCount (hPowers j) hMenus
  simpa only [List.map_map, Function.comp_def] using hFold

end CCO.TerminalLattice
