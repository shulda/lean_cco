import CCO.TerminalLattice.OriginalSparseRealizationReadout
import CCO.TerminalLattice.OriginalExternalLabels
import Mathlib.Data.Fintype.Basic

/-!
# B050 C35: ACTUAL K-diversity fine-atom frame of one realized sparse network

We encode all genuine fine ORIGINAL K-diversity atoms in a finite
palette, with no quotient-redacted action and no invented colour.
The one OLD global CCO/SAP injective network realization from C34 has
a true OLD centre-to-root fine atom in this palette at every vertex.
This produces a finite vertex colouring κ for the actual B006 sparse
labelled graph.

The monochromatic edge of EVERY actual external complete old-G
orbital label then yields the previously proved literal original
STRONG-square hits, simultaneously. This is a receiving theorem for a
concrete f, not an unconstructed global network hypothesis or reset.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- Exactly the genuine OLD fine diversity colours inside K.
No equality symbol, quotient diagonal, or abstract quotient atom. -/
abbrev OriginalKdivAtom {i : ι} (K : ColourEq S i) :=
  {c : S.Atom i i // c ∈ originalEquivDiversityPalette S K}

noncomputable instance originalKdivAtom_fintype {i : ι}
    (K : ColourEq S i) : Fintype (OriginalKdivAtom S K) := by
  letI : Fintype (S.Atom i i) := S.finiteAtom i i
  exact Fintype.ofFinite _

/-- A nonzero ORIGINAL equivalence supplies a genuine diversity fine
atom, hence a positive number of actual source vertex colours. -/
theorem originalKdivAtom_card_pos {i : ι}
    (K : ColourEq S i) (hK : (⊥ : ColourEq S i) < K) :
    0 < Fintype.card (OriginalKdivAtom S K) := by
  obtain ⟨c,hc⟩ := original_nonzero_Kdiv_nonempty S K hK
  exact Fintype.card_pos_iff.mpr ⟨⟨c,hc⟩⟩

/-- A finite exact enumeration of ACTUAL old K-diversity fine atoms.
The frame is an original fine palette, not a quotient orbital. -/
noncomputable def originalKdivFrame {i : ι}
    (K : ColourEq S i) :
    Fin (Fintype.card (OriginalKdivAtom S K)) → S.Atom i i :=
  fun j => ((Fintype.equivFin (OriginalKdivAtom S K)).symm j).val

/-- A real centre spoke of the one injective old private diagram
has some genuine fine OLD K-diversity colour in CENTRE-to-ROOT
orientation. The colour is read from the actual single CCO witness,
not chosen freely for each graph vertex. -/
theorem originalSparseRealization_spoke_Katom
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (f : DiagramHom (oldSparseWordDiagram S H sap W spoke words))
    (hInj : f.IsInjective)
    (v : Fin W.size) :
    ∃ c : OriginalKdivAtom S K,
      S.colour
        (originalSparseMarkedValue S H sap W spoke words f (oldSparseCentre W))
        (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W v)) =
          some c.val := by
  obtain ⟨c,hc,hCol⟩ :=
    originalSparseRealization_spoke_profile
      S H sap W spoke words f hInj v
  have hKc : c ∈ originalEquivDiversityPalette S K := by
    rw [← hSpoke]
    exact hc
  refine ⟨⟨c,hKc⟩, ?_⟩
  exact (colour_symmetric S
    (originalSparseMarkedValue S H sap W spoke words f (oldSparseCentre W))
    (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W v))).trans hCol

/-- The graph-vertex code is the finite index of its ACTUAL observed
old centre-to-root colour, using only finite old K-diversity atoms. -/
noncomputable def originalSparseRealization_vertexColour
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (f : DiagramHom (oldSparseWordDiagram S H sap W spoke words))
    (hInj : f.IsInjective)
    (v : Fin W.size) :
    Fin (Fintype.card (OriginalKdivAtom S K)) :=
  (Fintype.equivFin (OriginalKdivAtom S K))
    (Classical.choose
      (originalSparseRealization_spoke_Katom
        S H sap K W spoke words hSpoke f hInj v))

/-- Each code reads EXACTLY the true original OLD fine atom of the
single injective realization; no new edge-colour function or
hypothetical K-class representative is introduced. -/
theorem originalSparseRealization_vertexColour_spec
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (f : DiagramHom (oldSparseWordDiagram S H sap W spoke words))
    (hInj : f.IsInjective)
    (v : Fin W.size) :
    S.colour
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseCentre W))
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W v)) =
      some (originalKdivFrame S K
        (originalSparseRealization_vertexColour
          S H sap K W spoke words hSpoke f hInj v)) := by
  let c : OriginalKdivAtom S K :=
    Classical.choose
      (originalSparseRealization_spoke_Katom
        S H sap K W spoke words hSpoke f hInj v)
  have hCol := Classical.choose_spec
    (originalSparseRealization_spoke_Katom
      S H sap K W spoke words hSpoke f hInj v)
  change S.colour
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseCentre W))
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W v)) =
      some c.val at hCol
  change S.colour
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseCentre W))
      (originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W v)) =
      some ((Fintype.equivFin (OriginalKdivAtom S K)).symm
        ((Fintype.equivFin (OriginalKdivAtom S K)) c)).val
  simpa only [Equiv.symm_apply_apply] using hCol

/-- Source C35 genuine network-to-all-ORBITAL-hits receiving lemma:
one actual original injective old diagram f, source exact spoke and
edge-word profiles, and the original ambient-G COMPLETE external
orbital family yield ALL hits of the original quotient-orbital square.

The finite frame and colouring are constructed from f above and are
NOT inputs. The graph W really has the number of vertex colours
equal to the actual OLD K-diversity fine-atom count. -/
theorem originalSparseRealization_all_external_hits
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i)
    {r g : Nat} (hr : 0 < r)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph
      (Fintype.card (OriginalKdivAtom S K)) r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (menus : Fin r → S.Menu i i)
    (hWords : ∀ j : Fin r,
      PositiveWord.profile S (words j) = menus j)
    (hExternal : ∀ j : Fin r, ∀ c ∈ menus j,
      c ∉ originalEquivDiversityPalette S J)
    (hEnumerate : ∀ x y : X i, K x y → ¬ J x y →
      ∃ j : Fin r,
        menus j = originalQuotientOrbitalPalette S (G := G) J x y)
    (f : DiagramHom (oldSparseWordDiagram S H sap W spoke words))
    (hInj : f.IsInjective) :
    ∃ p z : X i, K p z ∧ ¬ J p z ∧
      ∀ x y : X i, K x y → ¬ J x y →
        (S.product
          (originalQuotientOrbitalPalette S (G := G) J p z)
          (originalQuotientOrbitalPalette S (G := G) J p z)
          ∩ originalQuotientOrbitalPalette S (G := G) J x y).Nonempty := by
  let o : X i :=
    originalSparseMarkedValue S H sap W spoke words f (oldSparseCentre W)
  let root : Fin W.size → X i := fun v =>
    originalSparseMarkedValue S H sap W spoke words f (oldSparseRoot W v)
  let frame : Fin (Fintype.card (OriginalKdivAtom S K)) →
      S.Atom i i := originalKdivFrame S K
  let κ : Fin W.size → Fin (Fintype.card (OriginalKdivAtom S K)) :=
    originalSparseRealization_vertexColour
      S H sap K W spoke words hSpoke f hInj
  have hSpokes : ∀ v, S.colour o (root v) = some (frame (κ v)) := by
    intro v
    exact originalSparseRealization_vertexColour_spec
      S H sap K W spoke words hSpoke f hInj v
  have hSpokeK : ∀ v, K o (root v) := by
    intro v
    exact originalSparseRealization_centre_K
      S H sap K W spoke words hSpoke f hInj v
  have hEdges : ∀ v w, W.graph.Adj v w →
      S.menuRel (menus (W.label s(v,w))) (root v) (root w) := by
    intro v w hAdj
    have hProf := originalSparseRealization_graph_profile
      S H sap W spoke words f hInj v w hAdj
    simpa only [hWords] using hProf
  exact original_realized_sparse_network_orbital_hits
    S (G := G) J K hr W frame κ o root menus
    hSpokes hSpokeK hEdges hExternal hEnumerate

end CCO.TerminalLattice
