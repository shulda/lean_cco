import CCO.Finite

/-!
# B002 C12: cycles avoiding the one formal root

For any typed partial diagram, a single assignment of ORIGINAL
real points that preserves every non-root edge immediately realizes
each simple cycle avoiding that root. This isolates the only
nontrivial cycle case in the private-fan Helly proof: cycles through
the formal root, which use two private paths and pairwise ball data.

This is a genuine proved restriction of real edge preservation,
not an assumed cycle extension theorem.
-/

universe u v w z

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Every simple cycle avoiding a designated root has an actual
homomorphism if its edges are preserved by a chosen old real-point
assignment away from that root. The root's value may be arbitrary. -/
theorem cycleHom_of_nonroot_edge_realization
    {V : Type z} (D : PartialDiagram S V) (root : V)
    (point : ∀ v : V, X (D.vertexSort v))
    (hNonroot : ∀ (v w : V)
        (hv : v ≠ root) (hw : w ≠ root)
        (hvw : v ≠ w)
        (a : S.Atom (D.vertexSort v) (D.vertexSort w)),
      D.edge v w hvw = some a →
        S.colour (point v) (point w) = some a)
    (C : SimpleCycle D)
    (hAvoid : ∀ p : Fin C.length, C.vertices p ≠ root) :
    CycleHom C := by
  refine ⟨fun p => point (C.vertices p), ?_⟩
  intro p a hEdge
  exact hNonroot (C.vertices p)
    (C.vertices (cyclicNext C.length_pos p))
    (hAvoid p)
    (hAvoid (cyclicNext C.length_pos p))
    (C.next_ne p) a hEdge

end CCO.RawExact
