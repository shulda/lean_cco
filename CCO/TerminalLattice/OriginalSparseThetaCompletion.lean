import CCO.TerminalLattice.OriginalSparseThetaCycleGuard
import CCO.TerminalLattice.OriginalCCOUniverseBridge

/-!
# B050 source08 C30 to C34: ONE original CCO completion of a genuine multi-theta diagram

The independent multiple-private-branch theta guard has already
established a real old colour-preserving homomorphism for EVERY
simple specified cycle of ONE source diagram. Here we apply the
original semantic homomorphic CCO hypothesis ONCE to the WHOLE
finite old typed diagram and invoke original AgeSAP injectivisation
through the accepted B001 completion theorem.

This does NOT assume a simultaneous root valuation, quotient CCO,
quotient SAP, reset square or any hypothetical source completion.
The positive private paths can pass through arbitrary old named sorts;
their spectra are only required to contain the specified original
same-sort guards. Bare spokes carry no original specified edge.

The explicit CCO input is used here and nowhere in the independent
source08 C26–C30 theta-cycle proof.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- A SINGLE global original CCO completion of the ACTUAL finite
old multi-theta sparse graph network, with original SAP separating
ALL formal vertices. The completed source instance is derived from
the exact original SOURCE CCO and the CCO-free cycle-guard theorem,
not from an assumed global completion oracle. -/
theorem originalSparseTheta_strongCompletion_of_original_CCO
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} {q r g N : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (hN : 0 < N) (hGirth : r * (N-1) + 1 ≤ g)
    (hContained : ∀ j : Fin r,
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K) :
    (originalSparseThetaDiagram
      S H sap W K hK spokes menus families hSpec).HasStrongCompletion := by
  have ccoZero : SemanticCCO.{u,v,0,w} S :=
    originalSemanticCCO_finite_universe_zero S cco
  apply (PartialDiagram.strongCompletion_iff_cycles_of_SAP_CCO
    H sap ccoZero
      (originalSparseThetaDiagram
        S H sap W K hK spokes menus families hSpec)).2
  exact originalSparseTheta_cycle_guard S H sap
    W K hK spokes menus families hSpec
      hN hGirth hContained hPowers

/-- The resulting strong completion is an ACTUAL old source
homomorphism which is simultaneously injective on ALL formal
roots and typed private interiors of ONE entire multi-branch
sparse network. This is strictly stronger than independent
cycle maps, and does not itself assert the later reset square. -/
theorem originalSparseTheta_injective_hom_of_original_CCO
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} {q r g N : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (hN : 0 < N) (hGirth : r * (N-1) + 1 ≤ g)
    (hContained : ∀ j : Fin r,
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K) :
    ∃ f : DiagramHom
      (originalSparseThetaDiagram
        S H sap W K hK spokes menus families hSpec),
      f.IsInjective :=
  originalSparseTheta_strongCompletion_of_original_CCO
    S H sap cco W K hK spokes menus families hSpec
      hN hGirth hContained hPowers

end CCO.TerminalLattice
