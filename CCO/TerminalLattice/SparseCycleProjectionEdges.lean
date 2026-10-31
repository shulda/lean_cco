import CCO.TerminalLattice.OptionalPositiveCycles
import CCO.TerminalLattice.SparseWordNetwork

/-!
# B050 C27: every projected edge is a REAL sparse graph or centre edge

We use the accepted B002 compressed marked-cycle label witness.
In our one-word-per-pair old diagram, a used marked edge must contain
the actual positive word selected for that pair, never an omitted
typed-Top edge. The concrete selection has only TWO possibilities:
a centre-to-graph-root spoke or an actual adjacent unordered edge
of the accepted B006 sparse labelled graph W.

No quotient-reduct action, fake top spoke, cycle-realization oracle,
or global original CCO completion appears here.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- A genuinely used canonical edge label of the B002 compressed
private diagram has a REAL positive original word. No graph geometry
is assumed; it follows from the literal occurrence slot index,
which cannot belong to an empty presentation. -/
theorem oldOptionalPositive_used_marked_edge_has_word
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words))
    (e : CCO.RawExact.QuotientExpansion.Edge n)
    (he : CCO.RawExact.CyclicSuppression.LabelOn
      (CCO.RawExact.QuotientExpansion.initialCycle S
        (fun _ : Fin n => i)
        (oldOptionalPositivePresentations S words)
        (oldOptionalPositivePresentations_nonempty S H sap words) C) e) :
    ∃ word : PositiveWord S i i, words e = some word := by
  let sort : Fin n → ι := fun _ => i
  let P := oldOptionalPositivePresentations S words
  let hNE := oldOptionalPositivePresentations_nonempty S H sap words
  obtain ⟨k, hk⟩ := he
  let o := CCO.RawExact.QuotientExpansion.cycleOccurrence S sort P hNE C k
  have hEdge : o.1 = e := by
    change (CCO.RawExact.QuotientExpansion.cycleOccurrence
      S sort P hNE C k).1 = e at hk
    exact hk
  have hBound : o.2.val < (P o.1).length := o.2.isLt
  have hLength : (P o.1).length = (P e).length :=
    congrArg (fun edge => (P edge).length) hEdge
  have hSlot : o.2.val < (P e).length := by omega
  cases hWords : words e with
  | none =>
      have hZero : (P e).length = 0 := by
        simp [P,oldOptionalPositivePresentations,hWords]
      omega
  | some word =>
      exact ⟨word,hWords⟩

/-- Elementary C27 literal sparse-edge support. An actual specified
positive word belongs EITHER to one edge ending at the unique LAST
centre, OR to a genuine W-adjacent unordered pair of distinct graph
roots. All other marked pairs have no private atom path at all.

The root indices are ACTUAL Fin W.size points with the SAME literal
ordered numeric endpoints as the canonical B002 marked-edge code. -/
theorem oldSparseWordSelection_present_is_star_or_graph
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (e : CCO.RawExact.QuotientExpansion.Edge (W.size+1))
    (hPresent : ∃ word : PositiveWord S i i,
      oldSparseWordSelection S W spoke words e = some word) :
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
      ⟨e.val.1.val, by have hl := e.property; have hr := e.val.2.isLt; omega⟩
    let y : Fin W.size :=
      ⟨e.val.2.val, by have hr := e.val.2.isLt; omega⟩
    have hAdj : W.graph.Adj x y := by
      by_contra hNo
      obtain ⟨word,hw⟩ := hPresent
      have hNone : oldSparseWordSelection S W spoke words e = none := by
        simp [oldSparseWordSelection,hCentre,x,y,hNo]
      rw [hNone] at hw
      cases hw
    exact ⟨x,y,rfl,rfl,hAdj⟩

/-- The genuine C27 marked projection of ANY concrete sparse-word
diagram cycle uses only edges of the ORIGINAL W graph together with
the real star to the unique centre. In particular no absent W-edge
can become a specified private path or appear in a compressed cycle.

This proves the skeleton SUPPORT component, not yet the cyclic
ordering/positive-word homomorphism for all compressed cycles. -/
theorem oldSparseWordDiagram_projected_edges_star_or_graph
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (C : SimpleCycle (oldSparseWordDiagram S H sap W spoke words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (oldOptionalPositivePresentations S
        (oldSparseWordSelection S W spoke words))
      (oldOptionalPositivePresentations_nonempty S H sap
        (oldSparseWordSelection S W spoke words)) C)
    (k : Fin B.length) :
    (B.edges k).val.2.val = W.size ∨
      ∃ (x y : Fin W.size),
        x.val = (B.edges k).val.1.val ∧
        y.val = (B.edges k).val.2.val ∧
        W.graph.Adj x y := by
  let selection := oldSparseWordSelection S W spoke words
  have hUsed : CCO.RawExact.CyclicSuppression.LabelOn
      (CCO.RawExact.QuotientExpansion.initialCycle S
        (fun _ : Fin (W.size+1) => i)
        (oldOptionalPositivePresentations S selection)
        (oldOptionalPositivePresentations_nonempty S H sap selection) C)
      (B.edges k) :=
    (B.labels_iff (B.edges k)).mpr ⟨k,rfl⟩
  obtain ⟨word,hWord⟩ :=
    oldOptionalPositive_used_marked_edge_has_word
      S H sap selection C (B.edges k) hUsed
  exact oldSparseWordSelection_present_is_star_or_graph
    S W spoke words (B.edges k) ⟨word,hWord⟩

end CCO.TerminalLattice
