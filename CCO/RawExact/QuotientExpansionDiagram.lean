import CCO.RawExact.QuotientExpansionReferences
import CCO.RawExact.FunctionalAtomEdges
import CCO.RawExact.TaggedColourConverse
import CCO.RawExact.FanRootSpokeExistence

/-!
# One genuine original-coloured quotient word expansion diagram

Every private edge label is the actual old colour of its reference
walk. Overlap uniqueness has already been proved, including multiple
direct words for one marked pair, so these local labels form a functional
converse-compatible specification on the genuine original atom palette.
-/

universe u v w

namespace CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))

/-- Every candidate is certified by one actual original RAW walk. -/
def Candidate (v w : Vertex S sort P)
    (a : S.Atom (vertexSort S sort P v) (vertexSort S sort P w)) : Prop :=
  ∃ (o : Occurrence S sort P) (p q : PathPosition S (word S sort P o)),
    pathAdjacent S (word S sort P o) p q ∧ v = atPosition S sort P o p ∧
      w = atPosition S sort P o q ∧
      taggedColour S (referencePoint S sort P hNonempty o p)
        (referencePoint S sort P hNonempty o q) =
        (⟨vertexSort S sort P v, vertexSort S sort P w, some a⟩ :
          Σ i : ι, Σ j : ι, Option (S.Atom i j))

theorem candidate_functional (v w : Vertex S sort P)
    (a b : S.Atom (vertexSort S sort P v) (vertexSort S sort P w))
    (ha : Candidate S sort P hNonempty v w a)
    (hb : Candidate S sort P hNonempty v w b) : a = b := by
  obtain ⟨o, p, q, hpq, hv, hw, hColour⟩ := ha
  obtain ⟨o', p', q', hpq', hv', hw', hColour'⟩ := hb
  have hSame := overlapping_edge_reference_colours S sort P hNonempty
    o o' p q p' q' hpq hpq' (hv.symm.trans hv') (hw.symm.trans hw')
  have hEncoded :
      (⟨vertexSort S sort P v, vertexSort S sort P w, some a⟩ :
        Σ i : ι, Σ j : ι, Option (S.Atom i j)) =
      (⟨vertexSort S sort P v, vertexSort S sort P w, some b⟩ :
        Σ i : ι, Σ j : ι, Option (S.Atom i j)) :=
    hColour.symm.trans (hSame.trans hColour')
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and, Option.some.injEq] using hEncoded

theorem candidate_reverse (v w : Vertex S sort P)
    (a : S.Atom (vertexSort S sort P v) (vertexSort S sort P w))
    (ha : Candidate S sort P hNonempty v w a) :
    Candidate S sort P hNonempty w v (S.conv a) := by
  obtain ⟨o, p, q, hpq, hv, hw, hColour⟩ := ha
  refine ⟨o, q, p, (pathAdjacent_symm S _ p q).mp hpq, hw, hv, ?_⟩
  exact (taggedColour_reverse_real S _ _).trans
    (congrArg (taggedColourConverse S) hColour)

noncomputable def edgeData : TypedAtomEdgeData S (Vertex S sort P) (vertexSort S sort P) where
  label := Candidate S sort P hNonempty
  functional := candidate_functional S sort P hNonempty
  converse := by
    intro v w a
    constructor
    · exact candidate_reverse S sort P hNonempty v w a
    · intro h
      simpa only [S.conv_invol] using candidate_reverse S sort P hNonempty w v (S.conv a) h

/-- A real finite partial diagram on the original source's typed
irreflexive atom language; it has exactly the expanded private edges. -/
noncomputable def diagram : PartialDiagram S (Vertex S sort P) :=
  TypedAtomEdgeData.toPartialDiagram S (edgeData S sort P hNonempty)

theorem diagram_edge_iff (v w : Vertex S sort P) (hvw : v ≠ w)
    (a : S.Atom (vertexSort S sort P v) (vertexSort S sort P w)) :
    (diagram S sort P hNonempty).edge v w hvw = some a ↔
      Candidate S sort P hNonempty v w a :=
  TypedAtomEdgeData.toPartialDiagram_edge_some_iff S (edgeData S sort P hNonempty) v w hvw a

/-- The actual diagram neither drops a genuine private diversity edge
nor adds a relation between unrelated private interiors. -/
theorem diagram_support_iff (v w : Vertex S sort P) (hvw : v ≠ w) :
    (∃ a : S.Atom (vertexSort S sort P v) (vertexSort S sort P w),
      (diagram S sort P hNonempty).edge v w hvw = some a) ↔
      Adjacent S sort P v w := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨o, p, q, hpq, hv, hw, _⟩ := (diagram_edge_iff S sort P hNonempty v w hvw a).mp ha
    exact ⟨o, p, q, hpq, hv, hw⟩
  · rintro ⟨o, p, q, hpq, hv, hw⟩
    obtain ⟨a, ha⟩ := genuineEdge_tagged_some_at_sorts S
      (referencePoint S sort P hNonempty o p) (referencePoint S sort P hNonempty o q)
      (vertexSort S sort P v) (vertexSort S sort P w)
      (by rw [hv]; exact referencePoint_sort S sort P hNonempty o p)
      (by rw [hw]; exact referencePoint_sort S sort P hNonempty o q)
      (referencePoint_genuine S sort P hNonempty o p q hpq)
    exact ⟨a, (diagram_edge_iff S sort P hNonempty v w hvw a).mpr
      ⟨o, p, q, hpq, hv, hw, ha⟩⟩

/-- Every source simple cycle of this actual diagram satisfies the
proved purely combinatorial private expansion adjacency. -/
theorem simpleCycle_adjacent (C : SimpleCycle (diagram S sort P hNonempty)) :
    ∀ k, Adjacent S sort P (C.vertices k) (C.vertices (cyclicNext C.length_pos k)) := by
  intro k
  exact (diagram_support_iff S sort P hNonempty _ _ (C.next_ne k)).mp (C.specified k)

end CCO.RawExact.QuotientExpansion
