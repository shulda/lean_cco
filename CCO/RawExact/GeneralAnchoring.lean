import CCO.RawExact.AtomicFans

/-!
# B002 C12/C18: abstract finite complete-centre anchoring

This isolates the part of the private-path anchored-fan argument that
does NOT depend on how private paths are constructed. Given an actual
finite typed partial diagram with a displayed *complete* induced centre
subdiagram, original homogeneity moves a CCO homomorphism by ONE
automorphism to fix all displayed centres simultaneously.

The simple-cycle homomorphism premise is explicit: a future C12
private-path construction must prove it, not assume it.
-/

universe u v w z

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Original-source automorphisms transport arbitrary genuine diagram
homomorphisms, including homomorphisms which identify nonadjacent
vertices. There is no source SAP or quotient hypothesis. -/
def moveDiagramHom
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {V : Type z} {D : PartialDiagram S V}
    (f : DiagramHom D) (g : G) : DiagramHom D where
  point := fun p => g • f.point p
  preserves_edge := by
    intro p q hpq a ha
    exact (S.colourInvariant_of_homogeneous H g
      (f.point p) (f.point q)).trans
      (f.preserves_edge p q hpq a ha)

/-- A complete literal finite centre diagram can be held fixed in a
homomorphic CCO completion using one original automorphism. This
generalizes the last step of the atomic fan proof to ANY actual
finite private-path graph, without manufacturing a group section.

All centre pairs with distinct formal indices have genuine specified
diversity atoms. Equality of a centre with itself is the real None
colour, never an invented diversity edge. -/
theorem anchored_CCO_completion
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,z,w} S)
    {V : Type z} (D : PartialDiagram S V)
    {I : Type (max u v)} [Finite I]
    (marks : I ↪ V)
    (centres : ∀ t : I, X (D.vertexSort (marks t)))
    (hCentres : ∀ (p q : I) (hpq : p ≠ q),
      ∃ a : S.Atom (D.vertexSort (marks p))
          (D.vertexSort (marks q)),
        D.edge (marks p) (marks q) (marks.injective.ne hpq) =
          some a ∧ S.colour (centres p) (centres q) = some a)
    (hCycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, ∀ t : I, f.point (marks t) = centres t := by
  obtain ⟨f⟩ := cco V D hCycles
  have hColours : ∀ p q : I,
      S.colour (f.point (marks p)) (f.point (marks q)) =
        S.colour (centres p) (centres q) := by
    intro p q
    by_cases hpq : p = q
    · subst q
      have h1 :
          S.colour (f.point (marks p)) (f.point (marks p)) = none :=
        (S.colour_none_iff _ _).mpr rfl
      have h2 : S.colour (centres p) (centres p) = none :=
        (S.colour_none_iff _ _).mpr rfl
      exact h1.trans h2.symm
    · obtain ⟨a, hEdge, hColour⟩ := hCentres p q hpq
      exact (f.preserves_edge (marks p) (marks q)
        (marks.injective.ne hpq) a hEdge).trans hColour.symm
  obtain ⟨g, hg⟩ := align_actual_centres S H
    (fun t : I => D.vertexSort (marks t))
    (fun t : I => f.point (marks t)) centres hColours
  refine ⟨moveDiagramHom S H f g, ?_⟩
  intro t
  exact hg t

end CCO.RawExact
