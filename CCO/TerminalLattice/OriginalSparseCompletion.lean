import CCO.TerminalLattice.SparseAllCycleHom
import CCO.StrongExact.CycleCompletion

/-!
# B050 C34: ONE actual original CCO completion of the entire sparse network

The previous C27/C33 construction proves cycle homomorphisms for EVERY
specified simple cycle of ONE concrete finite old typed private-word
diagram, without invoking CCO. We now apply the original semantic CCO
interface ONCE to this whole diagram, and the accepted original AgeSAP
injectivization to produce a simultaneously injective actual source
realization of ALL its formal vertices, including named-sort interiors.

The hypothesis here is the SOURCE original SemanticCCO, not a new
cycle-realization oracle, quotient CCO, global reset conclusion,
or conditional completion provider. The following C35 step must
read the actual fine centre-root and graph-edge colours of THIS
single injective realization before the reset square is discharged.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- Source C34: the ONE original B006 sparse-labelled/positive-word
partial diagram has an ACTUAL simultaneous injective completion.
The only new hypothesis relative to the C27 cycle theorem is the
original semantic CCO. Its single invocation and original SAP
injectivization are supplied by the already ACCEPTED B001
`strongCompletion_iff_cycles_of_SAP_CCO` theorem.

No synthetic edge, hidden quotient axiom, or new original source
condition is introduced. -/
theorem oldSparseWordDiagram_strongCompletion_of_original_CCO
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} {q r g N : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (menus : Fin r → S.Menu i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (hWords : ∀ j : Fin r,
      PositiveWord.profile S (words j) = menus j)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K)
    (hN : 0 < N)
    (hGirth : r * (N-1) + 1 ≤ g) :
    (oldSparseWordDiagram S H sap W spoke words).HasStrongCompletion := by
  apply (PartialDiagram.strongCompletion_iff_cycles_of_SAP_CCO
    H sap cco (oldSparseWordDiagram S H sap W spoke words)).2
  exact oldSparseWordDiagram_all_cyclesHom
    S H sap K W spoke words menus hSpoke hWords hMenus hPowers hN hGirth

/-- Exact readable C34 consequence: there exist ONE genuine OLD
diagram homomorphism and an injectivity proof for its image of
EVERY formal vertex. These ARE simultaneous values, and the
previous per-cycle root witnesses are not reused as a fictitious
global labelling. -/
theorem oldSparseWordDiagram_injective_hom_of_original_CCO
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} {q r g N : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (menus : Fin r → S.Menu i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (hWords : ∀ j : Fin r,
      PositiveWord.profile S (words j) = menus j)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K)
    (hN : 0 < N)
    (hGirth : r * (N-1) + 1 ≤ g) :
    ∃ f : DiagramHom (oldSparseWordDiagram S H sap W spoke words),
      f.IsInjective :=
  oldSparseWordDiagram_strongCompletion_of_original_CCO
    S H sap cco K W spoke words menus
      hSpoke hWords hMenus hPowers hN hGirth

end CCO.TerminalLattice
