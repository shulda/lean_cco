import CCO.TerminalLattice.OriginalLabelListThreshold
import CCO.ParityHasse.Sparse.Labelled

/-!
# B050 C29/C27: SATURATED literal ordered complement of a real W graph cycle

The accepted B006 sparse labelled graph supplies a high-girth simple graph
on actual original graph roots. For an INJECTIVE actual cyclic enumeration
of length n+1 with n>=2, the first n REAL graph edges form a genuine
complementary path to the LAST closing edge, in the SAME cyclic order.
This proof keeps exactly that order without a virtual edge-set
permutation or any invented shortcut.

No original CCO, quotient-reduct homogeneity, hidden SAP, or extra
source exactness is used. This is precisely the centre-free W-cycle
algebra needed before the private old word root assignment of C27.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- The literal ordered complementary path (all edges except the
LAST closing edge) of an actual B006 sparse graph cycle has STRONG
profile K°, when the FULL original external menus have common
eventual N-fold powers K° and every genuine graph label's menu
is nonempty inside K°.

The only nontrivial geometric step is applying the ACTUAL sparse
graph's `NoShortCycles` theorem to its own cyclic injective roots,
to show the complementary path has more than r*(N-1) edges.
The original finite list pigeonhole and same-sort STRONG source
algebra then prove the exact literal endpoint profile.

The actual B002 projection must still be identified with this
ordered graph cycle, with its real words oriented correctly.
-/
theorem originalSparseGraph_ordered_complementary_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i)
    {q r g N n : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (hGirth : r * (N-1) + 1 ≤ g)
    (hN : 0 < N) (hn : 2 ≤ n)
    (vertices : Fin (n+1) ↪ Fin W.size)
    (hEdges : ∀ p : Fin (n+1),
      W.graph.Adj (vertices p)
        (vertices (CCO.cyclicNext (Nat.succ_pos n) p)))
    (menus : Fin r → S.Menu i i)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K) :
    originalPositiveStrongPath S
      ((List.ofFn (fun k : Fin n =>
        menus (W.label s(vertices k.castSucc,vertices k.succ))))) =
      some (originalEquivDiversityPalette S K) := by
  have hLong : r * (N-1) < n := by
    by_contra hNot
    have hShort : n+1 ≤ g := by omega
    exact (W.noShortCycles (n+1)
      (by omega : 3 ≤ n+1) hShort vertices) hEdges
  let labels : List (Fin r) :=
    List.ofFn (fun k : Fin n =>
      W.label s(vertices k.castSucc,vertices k.succ))
  have hListLength : labels.length = n := List.length_ofFn
  have hLongList : r * (N-1) < labels.length := by
    simpa only [hListLength] using hLong
  have hSpectrum :=
    original_long_ordered_label_path_saturates
      S H sap K hN menus labels hLongList hMenus hPowers
  simpa only [labels, List.map_ofFn] using hSpectrum

end CCO.TerminalLattice
