import CCO.TerminalLattice.OriginalThetaCycleMenuReadout
import CCO.TerminalLattice.OriginalSparseThetaNetwork
import CCO.TerminalLattice.SparseCycleNoCentre

/-!
# B050 source08 C26–C29: true marked support and girth of OLD sparse theta cycles

A finite typed old private theta network has a finite LIST of positive
atomic words on each present pair, not necessarily a singleton.
The accepted B002 marked projection retains EVERY used canonical edge.

This module proves that every projected edge with a real private
occurrence is either one ORIGINAL labelled W edge or a spoke to the
single final centre. When the centre is absent, the projected cycle is
an injective simple cycle in the ORIGINAL W graph, so its length
STRICTLY exceeds the graph's original girth cutoff.

No quotient automorphisms, idealized root skeleton, original semantic
CCO, exact individual branch profiles or source weakening are used.
The centre-containing case and common old cyclic menu values remain
separate obligations.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- In any ACTUAL B002 compressed marked cycle of an original
multi-word theta diagram, each projected edge has a nonempty PRIVATE
branch family. Omitted pairs cannot be promoted to marked edges by
cycle suppression, even if their external menu is unconstrained. -/
theorem originalTheta_projected_edge_has_branch
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (families : CCO.RawExact.QuotientExpansion.Edge n →
      List (PositiveWord S i i))
    (guards : CCO.RawExact.QuotientExpansion.Edge n → S.Menu i i)
    (hGuard : ∀ e, families e ≠ [] →
      (guards e).Nonempty ∧
      ∀ p ∈ families e, guards e ⊆ PositiveWord.profile S p)
    (C : SimpleCycle (originalThetaDiagram S H sap families guards hGuard))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin n => i)
      (originalThetaPresentations S families)
      (originalThetaPresentations_nonempty S H sap families guards hGuard) C)
    (k : Fin B.length) :
    families (B.edges k) ≠ [] := by
  let P := originalThetaPresentations S families
  let hNE := originalThetaPresentations_nonempty
    S H sap families guards hGuard
  have hLabel :
      CCO.RawExact.CyclicSuppression.LabelOn
        (CCO.RawExact.QuotientExpansion.initialCycle
          S (fun _ : Fin n => i) P hNE C) (B.edges k) :=
    (B.labels_iff (B.edges k)).mpr ⟨k, rfl⟩
  obtain ⟨step, hStep⟩ := hLabel
  let o : CCO.RawExact.QuotientExpansion.Occurrence
      S (fun _ : Fin n => i) P :=
    CCO.RawExact.QuotientExpansion.cycleOccurrence
      S (fun _ : Fin n => i) P hNE C step
  have hSame : o.1 = B.edges k := hStep
  have hPositive : 0 < (P o.1).length := by
    have hBound := o.2.isLt
    omega
  intro hEmpty
  have hZero : (P (B.edges k)).length = 0 := by
    simp [P, originalThetaPresentations, hEmpty]
  have hLenEq : (P o.1).length = (P (B.edges k)).length :=
    congrArg (fun edge => (P edge).length) hSame
  omega

/-- Literal support of each present finite multi-theta family:
the final marked root is the sole centre, and every OTHER present
pair is an actually adjacent unordered W edge with its exact two
original graph endpoint indices. A missing W pair has EMPTY family. -/
theorem originalSparseThetaSelection_present_is_star_or_graph
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spokes : List (PositiveWord S i i))
    (families : Fin r → List (PositiveWord S i i))
    (e : CCO.RawExact.QuotientExpansion.Edge (W.size+1))
    (hPresent : originalSparseThetaSelection S W spokes families e ≠ []) :
    e.val.2.val = W.size ∨
      ∃ (x y : Fin W.size),
        x.val = e.val.1.val ∧
        y.val = e.val.2.val ∧
        W.graph.Adj x y := by
  classical
  by_cases hCentre : e.val.2.val = W.size
  · exact Or.inl hCentre
  · right
    let x : Fin W.size :=
      ⟨e.val.1.val, by
        have hl := e.property
        have hr := e.val.2.isLt
        omega⟩
    let y : Fin W.size :=
      ⟨e.val.2.val, by
        have hr := e.val.2.isLt
        omega⟩
    have hAdj : W.graph.Adj x y := by
      by_contra hNo
      have hNone : originalSparseThetaSelection S W spokes families e = [] := by
        simp [originalSparseThetaSelection, hCentre, x, y, hNo]
      exact hPresent hNone
    exact ⟨x, y, rfl, rfl, hAdj⟩

/-- The genuinely compressed marks of ANY original sparse theta
network cycle have only real W-graph edges and real centre spokes.
This holds with MANY private words per pair and with absent spokes. -/
theorem originalSparseTheta_projected_edges_star_or_graph
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (C : SimpleCycle
      (originalSparseThetaDiagram
        S H sap W K hK spokes menus families hSpec))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (originalThetaPresentations S
        (originalSparseThetaSelection S W spokes families))
      (originalThetaPresentations_nonempty S H sap
        (originalSparseThetaSelection S W spokes families)
        (originalSparseThetaGuard S W K menus)
        (originalSparseTheta_guards_valid
          S W K hK spokes menus families hSpec)) C)
    (k : Fin B.length) :
    (B.edges k).val.2.val = W.size ∨
      ∃ (x y : Fin W.size),
        x.val = (B.edges k).val.1.val ∧
        y.val = (B.edges k).val.2.val ∧
        W.graph.Adj x y := by
  have hBranch :=
    originalTheta_projected_edge_has_branch
      S H sap
      (originalSparseThetaSelection S W spokes families)
      (originalSparseThetaGuard S W K menus)
      (originalSparseTheta_guards_valid
        S W K hK spokes menus families hSpec) C B k
  exact originalSparseThetaSelection_present_is_star_or_graph
    S W spokes families (B.edges k) hBranch

/-- A compressed ORIGINAL multi-theta cycle avoiding the centre is
an actual simple W cycle, preserving the B002 cyclic order and actual
unoriented source edge endpoints. Injectivity comes from B002,
not from an assumed W-cycle skeleton. -/
theorem originalSparseTheta_projected_noCentre_graph_cycle
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (C : SimpleCycle
      (originalSparseThetaDiagram
        S H sap W K hK spokes menus families hSpec))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (originalThetaPresentations S
        (originalSparseThetaSelection S W spokes families))
      (originalThetaPresentations_nonempty S H sap
        (originalSparseThetaSelection S W spokes families)
        (originalSparseThetaGuard S W K menus)
        (originalSparseTheta_guards_valid
          S W K hK spokes menus families hSpec)) C)
    (hNoCentre : ∀ k : Fin B.length,
      B.vertices k ≠ oldSparseCentre W) :
    ∃ vertices : Fin B.length ↪ Fin W.size,
      ∀ k : Fin B.length,
        W.graph.Adj (vertices k)
          (vertices (CCO.cyclicNext B.length_pos k)) := by
  let toGraph : Fin B.length → Fin W.size :=
    fun k => ⟨(B.vertices k).val, by
      have hlt := (B.vertices k).isLt
      have hneq : (B.vertices k).val ≠ W.size := by
        intro heq
        apply hNoCentre k
        apply Fin.ext
        simpa [oldSparseCentre] using heq
      omega⟩
  have hInj : Function.Injective toGraph := by
    intro x y hxy
    apply B.vertices.injective
    apply Fin.ext
    simpa only [toGraph] using congrArg Fin.val hxy
  refine ⟨⟨toGraph, hInj⟩, ?_⟩
  intro k
  rcases originalSparseTheta_projected_edges_star_or_graph
      S H sap W K hK spokes menus families hSpec C B k with
    hCentre | ⟨x, y, hx, hy, hAdj⟩
  · have hRight :
        CCO.RawExact.QuotientExpansion.right (B.edges k) =
          oldSparseCentre W := by
      apply Fin.ext
      simpa [CCO.RawExact.QuotientExpansion.right, oldSparseCentre] using hCentre
    rcases B.endpoints k with ⟨_, hEnd⟩ | ⟨hStart, _⟩
    · exact False.elim
        (hNoCentre (CCO.cyclicNext B.length_pos k) (hEnd.trans hRight))
    · exact False.elim (hNoCentre k (hStart.trans hRight))
  · have hLeft :
        CCO.RawExact.QuotientExpansion.left (B.edges k) =
          oldSparseRoot W x := by
      apply Fin.ext
      simpa [CCO.RawExact.QuotientExpansion.left, oldSparseRoot] using hx.symm
    have hRight :
        CCO.RawExact.QuotientExpansion.right (B.edges k) =
          oldSparseRoot W y := by
      apply Fin.ext
      simpa [CCO.RawExact.QuotientExpansion.right, oldSparseRoot] using hy.symm
    rcases B.endpoints k with ⟨hStart, hEnd⟩ | ⟨hStart, hEnd⟩
    · have hVstart : toGraph k = x := by
        apply Fin.ext
        simpa [toGraph, oldSparseRoot] using congrArg Fin.val (hStart.trans hLeft)
      have hVend : toGraph (CCO.cyclicNext B.length_pos k) = y := by
        apply Fin.ext
        simpa [toGraph, oldSparseRoot] using congrArg Fin.val (hEnd.trans hRight)
      simpa [hVstart, hVend] using hAdj
    · have hVstart : toGraph k = y := by
        apply Fin.ext
        simpa [toGraph, oldSparseRoot] using congrArg Fin.val (hStart.trans hRight)
      have hVend : toGraph (CCO.cyclicNext B.length_pos k) = x := by
        apply Fin.ext
        simpa [toGraph, oldSparseRoot] using congrArg Fin.val (hEnd.trans hLeft)
      simpa [hVstart, hVend] using W.graph.adj_symm hAdj

/-- The ORIGINAL girth certificate applies directly to the REAL
centre-free B002 projection of the multi-theta network. Its cyclic
length strictly exceeds g, so its complementary ordered path has the
sharp length needed for the C29 repeated-label saturation argument. -/
theorem originalSparseTheta_projected_noCentre_long
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (C : SimpleCycle
      (originalSparseThetaDiagram
        S H sap W K hK spokes menus families hSpec))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (originalThetaPresentations S
        (originalSparseThetaSelection S W spokes families))
      (originalThetaPresentations_nonempty S H sap
        (originalSparseThetaSelection S W spokes families)
        (originalSparseThetaGuard S W K menus)
        (originalSparseTheta_guards_valid
          S W K hK spokes menus families hSpec)) C)
    (hNoCentre : ∀ k : Fin B.length,
      B.vertices k ≠ oldSparseCentre W) :
    g < B.length := by
  obtain ⟨vertices, hEdges⟩ :=
    originalSparseTheta_projected_noCentre_graph_cycle
      S H sap W K hK spokes menus families hSpec C B hNoCentre
  by_contra hShort
  have hLen : B.length ≤ g := Nat.le_of_not_gt hShort
  exact (W.noShortCycles B.length B.length_ge_three hLen vertices) hEdges

end CCO.TerminalLattice
