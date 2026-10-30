import CCO.RawExact.QuotientExpansionWholeCycleClassification

/-!
# Source-free finite private-path graphs

The only input is a finite list of positive path lengths for each marked
unordered pair. A fixed one-colour encoding provides a `PartialDiagram`
representation of the uncoloured graph. Its carrier Nat is only a way to
construct that representation: it adds no source, group action, exactness,
CCO, or realization hypothesis to any graph theorem below. Empty lists
attach zero paths and retain their marked vertices. Coincident direct
paths are represented by the same graph edge.
-/

namespace CCO.SimultaneousQuotients.Private

open CCO.RawExact

/-- The fixed complete one-colour structure used solely to encode an
uncoloured formal graph. No automorphisms or source property is required. -/
private def encoding : AtomicSource Unit (fun _ => Nat) where
  Atom := fun _ _ => Unit
  finiteSort := inferInstance
  finiteAtom := fun _ _ => inferInstance
  nonemptySort := fun _ => inferInstance
  conv := fun a => a
  conv_invol := fun _ => rfl
  symmetricLoop := fun _ => rfl
  colour := fun x y => if x = y then none else some ()
  colour_none_iff := by
    intro i j x y
    cases i
    cases j
    simp
  colour_swap := by
    intro i j x y a
    cases a
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  realized := by
    intro i j a
    cases a
    exact ⟨0, 1, by decide⟩

private def encodingWord : Nat → RawWord encoding () ()
  | 0 => .nil ()
  | n + 1 => .atom () (encodingWord n)

private theorem encodingWord_length (n : Nat) :
    diversityLength encoding (encodingWord n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [encodingWord, diversityLength] using congrArg Nat.succ ih

private theorem encodingWord_relation (n : Nat) (hPos : 0 < n) (x y : Nat) (hxy : x ≠ y) :
    RawWord.relation encoding (encodingWord n) x y := by
  induction n generalizing x y with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          refine ⟨y, ?_, rfl⟩
          simp [AtomicSource.atomRel, encoding, hxy]
      | succ n =>
          let z := max x y + 1
          have hxz : x ≠ z := by dsimp [z]; omega
          have hzy : z ≠ y := by dsimp [z]; omega
          exact ⟨z, by simp [AtomicSource.atomRel, encoding, hxz], ih (by omega) z y hzy⟩

/-- A canonical orientation of a simple marked base edge. -/
abbrev Edge := QuotientExpansion.Edge

/-- All formal length data, including empty lists over top or absent edges. -/
structure Data (n : Nat) where
  lengths : Edge n → List Nat
  positive : ∀ e L, L ∈ lengths e → 0 < L

namespace Data
variable {n : Nat} (P : Data n)

private def menus : QuotientExpansion.Menus encoding (fun _ : Fin n => ()) :=
  fun e => (P.lengths e).map encodingWord

private theorem menus_nonempty (e : Edge n) :
    TRel.Nonempty (evaluate encoding (menus P e)) := by
  refine ⟨0, 1, ?_⟩
  intro word hWord
  obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hWord
  exact encodingWord_relation L (P.positive e L hL) 0 1 (by decide)

/-- Marked vertices plus disjoint strict interiors of individual paths.
This is a finite formal type; the encoding's Nat points are not vertices. -/
abbrev Vertex := QuotientExpansion.Vertex encoding (fun _ : Fin n => ()) (menus P)

def mark (m : Fin n) : P.Vertex := QuotientExpansion.mark encoding _ (menus P) m

/-- The actual simple, uncoloured private-path expansion. -/
noncomputable def diagram : PartialDiagram encoding P.Vertex :=
  QuotientExpansion.diagram encoding (fun _ => ()) (menus P) (menus_nonempty P)

/-- An ordinary finite simple cycle of the uncoloured expansion. -/
abbrev Cycle := SimpleCycle P.diagram

/-- The representation names exactly the successive-position graph
edges. In particular it introduces no parallel direct edge or fake loop. -/
theorem diagram_support (v w : P.Vertex) (hvw : v ≠ w) :
    (∃ a, P.diagram.edge v w hvw = some a) ↔
      QuotientExpansion.Adjacent encoding (fun _ => ()) (menus P) v w :=
  QuotientExpansion.diagram_support_iff encoding _ (menus P) (menus_nonempty P) v w hvw

/-- No simple cycle can leave a private path at one of its internal
positions. Touching one interior traverses every vertex and every edge. -/
theorem whole_path (C : P.Cycle)
    (o : QuotientExpansion.Occurrence encoding (fun _ : Fin n => ()) (menus P))
    (p : QuotientExpansion.Interior encoding (fun _ : Fin n => ()) (menus P) o)
    (hp : CycleVertex C (QuotientExpansion.interior encoding _ (menus P) o p)) :
    (∀ q, CycleVertex C (QuotientExpansion.atPosition encoding _ (menus P) o q)) ∧
    (∀ q r, pathAdjacent encoding (QuotientExpansion.word encoding _ (menus P) o) q r →
      CycleEdge C (QuotientExpansion.atPosition encoding _ (menus P) o q)
        (QuotientExpansion.atPosition encoding _ (menus P) o r)) :=
  QuotientExpansion.whole_path_on_cycle_of_interior encoding _ (menus P) C
    (QuotientExpansion.simpleCycle_adjacent encoding _ (menus P) (menus_nonempty P) C) o p hp

/-- Every raw simple cycle consists either of exactly two DISTINCT WHOLE
paths over ONE simple base edge (equality of both vertex and edge support),
or projects to a genuine SIMPLE cycle on distinct marked vertices.
No group/source/CCO/exactness premise occurs: `P` is just finite length data. -/
theorem cycle_classification (C : P.Cycle) :
    (∃ (e : Edge n)
      (first second : QuotientExpansion.Occurrence encoding (fun _ : Fin n => ()) (menus P)),
      first.1 = e ∧ second.1 = e ∧ first ≠ second ∧
      0 < diversityLength encoding (QuotientExpansion.word encoding _ (menus P) first) ∧
      0 < diversityLength encoding (QuotientExpansion.word encoding _ (menus P) second) ∧
      (∀ v, CycleVertex C v ↔
        (∃ p, QuotientExpansion.atPosition encoding _ (menus P) first p = v) ∨
        (∃ p, QuotientExpansion.atPosition encoding _ (menus P) second p = v)) ∧
      (∀ v w, CycleEdge C v w ↔
        QuotientExpansion.OccurrenceEdge encoding _ (menus P) first v w ∨
        QuotientExpansion.OccurrenceEdge encoding _ (menus P) second v w)) ∨
    Nonempty (QuotientExpansion.MarkedProjection encoding (fun _ => ()) (menus P) (menus_nonempty P) C) :=
  QuotientExpansion.cycle_two_whole_paths_or_marked_projection encoding _ (menus P) (menus_nonempty P) C

/-- There is no internal-only simple cycle: every cycle has at least two
DISTINCT marked vertices, independent of all colours and realizations. -/
theorem cycle_has_two_marks (C : P.Cycle) :
    ∃ m r : Fin n, m ≠ r ∧ CycleVertex C (P.mark m) ∧ CycleVertex C (P.mark r) := by
  let k : Fin C.length := ⟨0, C.length_pos⟩
  let e := (QuotientExpansion.initialCycle encoding (fun _ => ()) (menus P) (menus_nonempty P) C).label k
  have he : CyclicSuppression.LabelOn
      (QuotientExpansion.initialCycle encoding (fun _ => ()) (menus P) (menus_nonempty P) C) e := ⟨k, rfl⟩
  have hEnds := QuotientExpansion.used_label_endpoints encoding (fun _ => ())
    (menus P) (menus_nonempty P) C e he
  exact ⟨QuotientExpansion.left e, QuotientExpansion.right e,
    QuotientExpansion.left_ne_right e, hEnds.1, hEnds.2⟩

/-- A projected marked edge is an actual base edge carrying a path;
empty lists (including top blocks) cannot create marked-cycle edges. -/
theorem projected_edge_has_path (C : P.Cycle)
    (B : QuotientExpansion.MarkedProjection encoding (fun _ => ()) (menus P) (menus_nonempty P) C)
    (k : Fin B.length) : P.lengths (B.edges k) ≠ [] := by
  have hLabel := (B.labels_iff (B.edges k)).mpr ⟨k, rfl⟩
  obtain ⟨j, hj⟩ := hLabel
  let o := QuotientExpansion.cycleOccurrence encoding (fun _ => ()) (menus P) (menus_nonempty P) C j
  have ho : o.1 = B.edges k := hj
  have hBound := o.2.isLt
  intro hNil
  have hLength : (menus P o.1).length = 0 := by
    simp only [menus, ho, hNil, List.map_nil, List.length_nil]
  omega


/-- Marked endpoints remain literally distinct formal vertices, even when
no path is attached. Their future homomorphic images may still collide. -/
theorem mark_injective : Function.Injective P.mark := by
  intro x y hxy
  exact Sum.inl.inj hxy

/-- Zero restrictions create no edges and do not create equality paths. -/
theorem no_edges_of_empty (hEmpty : ∀ e, P.lengths e = [])
    (v w : P.Vertex) (hvw : v ≠ w) : P.diagram.edge v w hvw = none := by
  cases hc : P.diagram.edge v w hvw with
  | none => rfl
  | some a =>
      have hAdj := (P.diagram_support v w hvw).mp ⟨a, hc⟩
      obtain ⟨o, _, _, _, _, _⟩ := hAdj
      have hBound := o.2.isLt
      have hZero : (menus P o.1).length = 0 := by simp only [menus, hEmpty, List.map_nil, List.length_nil]
      omega

/-- Retained isolated marked vertices contribute no artificial cycle. -/
theorem no_cycles_of_empty (hEmpty : ∀ e, P.lengths e = []) : IsEmpty P.Cycle := by
  refine ⟨fun C => ?_⟩
  let k : Fin C.length := ⟨0, C.length_pos⟩
  obtain ⟨a, ha⟩ := C.specified k
  rw [P.no_edges_of_empty hEmpty _ _ (C.next_ne k)] at ha
  cases ha


end Data
end CCO.SimultaneousQuotients.Private
