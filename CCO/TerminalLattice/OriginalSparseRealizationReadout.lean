import CCO.TerminalLattice.OriginalSparseCompletion
import CCO.TerminalLattice.SparseWordMarkedEdges
import CCO.TerminalLattice.RealizedNetworkReset

/-!
# B050 C35: read the ACTUAL single original CCO/SAP sparse realization

All vertices used here are images of the literal B002 marked vertices
of ONE original sparse private positive-word network. We use the
previously proved original positive STRONG profile readout only AFTER
the actual full-network homomorphism has been injectivized.

Spokes give a true old K-diversity menu from each marked graph root to
the one old centre. Each genuinely adjacent W root pair has the exact
original STRONG menu of its own full old-G label. No unprescribed edge
is assigned an atom; neither a quotient automorphism nor a second CCO
application occurs.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- The image of a literal old marked vertex of the ONE sparse
private-word diagram. No choice of another realization is made. -/
def originalSparseMarkedValue
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (f : DiagramHom (oldSparseWordDiagram S H sap W spoke words))
    (p : Fin (W.size+1)) : X i :=
  f.point (CCO.RawExact.QuotientExpansion.mark S
    (fun _ : Fin (W.size+1) => i)
    (oldOptionalPositivePresentations S
      (oldSparseWordSelection S W spoke words)) p)

/-- The genuine old coloured spoke in the simultaneous injective
source realization, retaining the ORIGINAL ROOT-to-CENTRE word
orientation. This is not an arbitrary chosen fine atom. -/
theorem originalSparseRealization_spoke_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (f : DiagramHom (oldSparseWordDiagram S H sap W spoke words))
    (hInj : f.IsInjective) (v : Fin W.size) :
    S.menuRel (PositiveWord.profile S spoke)
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W v))
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseCentre W)) := by
  have h := oldOptionalPositiveDiagram_hom_strong_profile
    S H sap (oldSparseWordSelection S W spoke words)
    f hInj (oldSparseSpokeMarkedEdge W v) spoke
    (oldSparseWordSelection_spoke S W spoke words v)
  exact h

/-- In its true ascending canonical orientation, each REAL graph
edge is realized with the STRONG endpoint menu of its actual
specified positive old typed word. -/
theorem originalSparseRealization_graph_profile_ascending
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (f : DiagramHom (oldSparseWordDiagram S H sap W spoke words))
    (hInj : f.IsInjective)
    (x y : Fin W.size) (hxy : x < y) (hAdj : W.graph.Adj x y) :
    S.menuRel (PositiveWord.profile S (words (W.label s(x,y))))
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W x))
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W y)) := by
  have h := oldOptionalPositiveDiagram_hom_strong_profile
    S H sap (oldSparseWordSelection S W spoke words)
    f hInj (oldSparseGraphMarkedEdge W x y hxy)
    (words (W.label s(x,y)))
    (oldSparseWordSelection_graph S W spoke words x y hxy hAdj)
  exact h

/-- Original same-sort colour symmetry makes ANY genuine old
same-sort menu relation symmetric, without requiring a quotient
group or a symmetric positive WORD syntax. -/
theorem original_same_sort_menuRel_symm
    {i : ι} (M : S.Menu i i) (x y : X i)
    (h : S.menuRel M x y) : S.menuRel M y x := by
  obtain ⟨a,ha,hcol⟩ := h
  exact ⟨a,ha,(colour_symmetric S y x).trans hcol⟩

/-- Every genuine unoriented W edge, in EITHER ordered direction,
has its own exact original label-specific whole positive-word
STRONG menu. This is a property of the ONE injective homomorphism;
it does not assume a preexisting global root-table oracle. -/
theorem originalSparseRealization_graph_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (f : DiagramHom (oldSparseWordDiagram S H sap W spoke words))
    (hInj : f.IsInjective)
    (x y : Fin W.size) (hAdj : W.graph.Adj x y) :
    S.menuRel (PositiveWord.profile S (words (W.label s(x,y))))
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W x))
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W y)) := by
  by_cases hxy : x < y
  · exact originalSparseRealization_graph_profile_ascending
      S H sap W spoke words f hInj x y hxy hAdj
  · have hyx : y < x := lt_of_le_of_ne
      (le_of_not_gt hxy) (by
        intro h
        subst y
        exact W.graph.irrefl x hAdj)
    have hRev := originalSparseRealization_graph_profile_ascending
      S H sap W spoke words f hInj y x hyx (W.graph.symm hAdj)
    have hRev' : S.menuRel (PositiveWord.profile S (words (W.label s(x,y))))
        (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W y))
        (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W x)) := by
      simpa only [Sym2.eq_swap] using hRev
    exact original_same_sort_menuRel_symm S _ _ _ hRev'

/-- Every actual root and the common centre are ORIGINAL K-related,
because their genuinely specified spoke has its old K-diversity
profile. The same source fine-atom invariant equivalence is used,
not any K relation on a quotient. -/
theorem originalSparseRealization_centre_K
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (f : DiagramHom (oldSparseWordDiagram S H sap W spoke words))
    (hInj : f.IsInjective) (v : Fin W.size) :
    K (originalSparseMarkedValue S H sap W spoke words f (oldSparseCentre W))
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W v)) := by
  obtain ⟨a,ha,hColour⟩ :=
    originalSparseRealization_spoke_profile
      S H sap W spoke words f hInj v
  rw [hSpoke] at ha
  obtain ⟨p,q,hKpq,hPQColour⟩ := ha
  have hKroot :
      K (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W v))
        (originalSparseMarkedValue S H sap W spoke words f (oldSparseCentre W)) :=
    (K.property p q _ _
      (hPQColour.trans hColour.symm)).mp hKpq
  exact K.val.symm hKroot

end CCO.TerminalLattice
