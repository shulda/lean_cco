import CCO.CloneTupleGeometry.MarkedChildSourceEquiv

/-!
# B060 N02: genuine homomorphic CCO transport along a complete source isomorphism

Map only the specified diversity edges of a partial diagram through the
actual atom bijections. The finite vertex set, missing edges and simple
cycle indices stay unchanged. Each independent cycle witness maps through
the point bijections; one whole target homomorphism pulls back to the
source. Logical equality is never inserted as a diversity constraint.
-/

universe u v w z
namespace CCO.CloneTupleGeometry.TypedAtomicSourceEquiv

variable {ι : Type u} {X Y : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} ι Y}
variable (E : TypedAtomicSourceEquiv S T)
variable {V : Type z}

/-- Literal atom-name transport of the same partial diagram. -/
def mapDiagram (D : PartialDiagram S V) : PartialDiagram T V where
  finite_type := D.finite_type
  vertexSort := D.vertexSort
  edge x y h := (D.edge x y h).map (E.atom (D.vertexSort x) (D.vertexSort y))
  edge_reverse := by
    intro x y h a
    constructor
    · intro ha
      obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
      rw [(D.edge_reverse x y h b).mp hb]
      change some (E.atom _ _ (S.conv b)) = some (T.conv (E.atom _ _ b))
      exact congrArg some (E.preserves_conv b)
    · intro ha
      obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
      rw [(D.edge_reverse y x h.symm b).mp hb]
      change some (E.atom _ _ (S.conv b)) = some a
      rw [E.preserves_conv,he,T.conv_invol]

theorem mapDiagram_edge_iff (D : PartialDiagram S V)
    (x y : V) (h : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) :
    (mapDiagram E D).edge x y h =
        some (E.atom (D.vertexSort x) (D.vertexSort y) a) ↔
      D.edge x y h = some a := by
  constructor
  · intro ha
    obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
    exact hb.trans (congrArg some ((E.atom _ _).injective he))
  · intro ha
    change (D.edge x y h).map (E.atom _ _) = some (E.atom _ _ a)
    rw [ha]
    rfl

/-- Every simple cycle in the renamed diagram is the SAME indexed
simple cycle in the original diagram; no injectivity of its eventual
source realization is added. -/
def unmapCycle (D : PartialDiagram S V)
    (K : SimpleCycle (mapDiagram E D)) : SimpleCycle D where
  length := K.length
  length_ge_three := K.length_ge_three
  length_pos := K.length_pos
  vertices := K.vertices
  next_ne := K.next_ne
  specified := by
    intro p
    obtain ⟨a,ha⟩ := K.specified p
    obtain ⟨b,hb,_⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨b,hb⟩

theorem mapDiagram_cycles (D : PartialDiagram S V)
    (cycles : ∀ K : SimpleCycle D, CycleHom K) :
    ∀ K : SimpleCycle (mapDiagram E D), CycleHom K := by
  intro K
  obtain ⟨p,hp⟩ := cycles (unmapCycle E D K)
  refine ⟨fun k => E.point _ (p k),?_⟩
  intro k a ha
  obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
  have hc := hp k b hb
  simpa only [hc,Option.map_some] using
    E.colour (p k) (p (cyclicNext K.length_pos k))

/-- Pull back the ONE actual whole-diagram homomorphism. This preserves
all specified old edges and requires no coherent choice of cycle witnesses. -/
def pullDiagramHom (D : PartialDiagram S V)
    (f : DiagramHom (mapDiagram E D)) : DiagramHom D where
  point x := (E.point (D.vertexSort x)).symm (f.point x)
  preserves_edge := by
    intro x y h a ha
    apply Option.map_injective (E.atom (D.vertexSort x) (D.vertexSort y)).injective
    calc
      (S.colour
          ((E.point (D.vertexSort x)).symm (f.point x))
          ((E.point (D.vertexSort y)).symm (f.point y))).map
          (E.atom (D.vertexSort x) (D.vertexSort y)) =
        T.colour (f.point x) (f.point y) := by
          simpa only [Equiv.apply_symm_apply] using
            (E.colour
              ((E.point (D.vertexSort x)).symm (f.point x))
              ((E.point (D.vertexSort y)).symm (f.point y))).symm
      _ = some (E.atom (D.vertexSort x) (D.vertexSort y) a) :=
        f.preserves_edge x y h _ ((mapDiagram_edge_iff E D x y h a).mpr ha)
      _ = (some a).map (E.atom (D.vertexSort x) (D.vertexSort y)) := rfl

/-- Homomorphic simple-cycle completion transports along an actual
complete source isomorphism in EVERY formal-vertex universe. -/
theorem semanticCCO_pullback (cco : SemanticCCO.{u,v,z,w} T) :
    SemanticCCO.{u,v,z,w} S := by
  intro V D cycles
  obtain ⟨f⟩ := cco V (mapDiagram E D) (mapDiagram_cycles E D cycles)
  exact ⟨pullDiagramHom E D f⟩

end CCO.CloneTupleGeometry.TypedAtomicSourceEquiv
