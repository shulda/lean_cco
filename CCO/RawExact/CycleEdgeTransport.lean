import CCO.Finite

/-!
# B002 C12: transport a simple cycle's specified edge across endpoint equality

The `SimpleCycle.specified` field has dependent ORIGINAL atom
palettes indexed by its actual adjacent formal vertices, and
`PartialDiagram.edge` also takes a proof that those vertices differ.
Rewriting vertex identities naively inside such a dependent edge
proof is invalid. These lemmas use genuine equality elimination
on freely named endpoints, carrying the entire old atom and edge
proof together without any axiom, cast shortcut or fake edge.
-/

universe u v w z

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} {D : PartialDiagram S V}

/-- Transport a specified cycle edge's entire existential
old atomic label to two equal explicitly named endpoints. -/
theorem simpleCycle_specified_at_vertices
    (C : SimpleCycle D) (p : Fin C.length)
    (v w : V)
    (hV : C.vertices p = v)
    (hW : C.vertices (cyclicNext C.length_pos p) = w)
    (hvw : v ≠ w) :
    ∃ a : S.Atom (D.vertexSort v) (D.vertexSort w),
      D.edge v w hvw = some a := by
  cases hV
  cases hW
  exact C.specified p

/-- If a real assignment correctly preserves the one FULL
option-valued edge between named equal endpoints, it also
preserves ANY specified original atomic label of that cycle
edge. Equality elimination avoids all dependent proof casts. -/
theorem simpleCycle_preserve_at_vertices
    (C : SimpleCycle D) (p : Fin C.length)
    (v w : V)
    (hV : C.vertices p = v)
    (hW : C.vertices (cyclicNext C.length_pos p) = w)
    (hvw : v ≠ w)
    (point : ∀ t : V, X (D.vertexSort t))
    (hColour : S.colour (point v) (point w) = D.edge v w hvw)
    (a : S.Atom
      (D.vertexSort (C.vertices p))
      (D.vertexSort (C.vertices (cyclicNext C.length_pos p))))
    (ha : D.edge (C.vertices p)
      (C.vertices (cyclicNext C.length_pos p))
      (C.next_ne p) = some a) :
    S.colour (point (C.vertices p))
      (point (C.vertices (cyclicNext C.length_pos p))) = some a := by
  cases hV
  cases hW
  exact hColour.trans ha

end CCO.RawExact
