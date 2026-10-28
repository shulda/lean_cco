import CCO.RawExact.FanFullEdgeSemantics
import CCO.RawExact.FanCycleAvoidance

/-!
# B002 C12: all full private-fan cycles that avoid the formal root

The complete full fan's nonroot edges are literally those of the
punctured source-realized fan diagram. Any specified simple cycle
avoiding the distinguished root is therefore homomorphically
realized by the one independently chosen original reference map,
even if it visits private interiors or repeats old sort labels.

The only cycles needing pairwise-ball compatibility are those that
contain the root. This avoids an unnecessary complete cycle-shape
classification in the source C13 proof.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A root-avoiding simple cycle of the FULL source-coloured
private fan has an unconditional real source homomorphism
under the original homogeneity assumptions for its word paths. -/
theorem privateFanFull_cycles_avoiding_root
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (C : SimpleCycle (privateFanFullDiagram S H D centres))
    (hAvoid : ∀ p : Fin C.length,
      C.vertices p ≠ privateFanRoot S D centres) :
    CycleHom C := by
  let f := privateFanPuncturedDiagram_realization S H D centres
  refine ⟨fun p => f.point (C.vertices p), ?_⟩
  intro p a ha
  have hv := hAvoid p
  have hw := hAvoid (cyclicNext C.length_pos p)
  have hSame := privateFanFull_nonroot_edge_eq S H D centres
    (C.vertices p)
    (C.vertices (cyclicNext C.length_pos p))
    hv hw (C.next_ne p)
  rw [hSame] at ha
  exact f.preserves_edge
    (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
    (C.next_ne p) a ha

end CCO.RawExact
