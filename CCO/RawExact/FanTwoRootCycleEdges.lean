import CCO.RawExact.CycleIncidence
import Mathlib.Tactic

/-!
# B002 C12: exactly two simple-cycle edges may meet one selected root

In a genuine simple cycle, any selected formal vertex occurs only
once. Consequently, only its unique outgoing edge and its unique
incoming edge can touch it; every other cycle edge has BOTH
endpoints different from that root.

This elementary fully typed cycle fact is the combinatorial
basis of the two-walk replacement proof of private-fan C12:
it avoids a long classification of all full private paths
traversed by the cycle.
-/

universe u v w z

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} {D : PartialDiagram S V}

/-- The only two edges of a specified simple cycle that can
touch a chosen formal root are the incoming and outgoing edges
at its unique position. Both endpoints of every other edge
are distinct from the root. -/
theorem cycle_edges_away_from_root_except_two
    (C : SimpleCycle D) (r : V)
    (p0 : Fin C.length)
    (hp0 : C.vertices p0 = r)
    (prev : Fin C.length)
    (hprev : cyclicNext C.length_pos prev = p0)
    (p : Fin C.length)
    (hp : p ≠ p0)
    (hNotPrev : p ≠ prev) :
    C.vertices p ≠ r ∧
    C.vertices (cyclicNext C.length_pos p) ≠ r := by
  constructor
  · intro hRoot
    exact hp (C.vertices.injective (hRoot.trans hp0.symm))
  · intro hRoot
    have hNext : cyclicNext C.length_pos p = p0 :=
      C.vertices.injective (hRoot.trans hp0.symm)
    have hEqual : cyclicNext C.length_pos p =
        cyclicNext C.length_pos prev :=
      hNext.trans hprev.symm
    exact hNotPrev ((cyclicNext_injective C.length_pos) hEqual)

/-- Given concrete preservation of the two distinguished cycle
edges and all remaining cycle edges, combine them into one
actual source cycle homomorphism. There is no assumption that
any other vertices are mapped injectively. -/
theorem cycleHom_of_two_checked_edges
    (C : SimpleCycle D)
    (point : ∀ v : V, X (D.vertexSort v))
    (p0 prev : Fin C.length)
    (hOther : ∀ p : Fin C.length,
      p ≠ p0 → p ≠ prev →
      ∀ a : S.Atom
          (D.vertexSort (C.vertices p))
          (D.vertexSort (C.vertices (cyclicNext C.length_pos p))),
        D.edge (C.vertices p)
          (C.vertices (cyclicNext C.length_pos p))
          (C.next_ne p) = some a →
        S.colour (point (C.vertices p))
          (point (C.vertices (cyclicNext C.length_pos p))) = some a)
    (hFirst : ∀ a : S.Atom
        (D.vertexSort (C.vertices p0))
        (D.vertexSort (C.vertices (cyclicNext C.length_pos p0))),
      D.edge (C.vertices p0)
        (C.vertices (cyclicNext C.length_pos p0))
        (C.next_ne p0) = some a →
      S.colour (point (C.vertices p0))
        (point (C.vertices (cyclicNext C.length_pos p0))) = some a)
    (hPrev : ∀ a : S.Atom
        (D.vertexSort (C.vertices prev))
        (D.vertexSort (C.vertices (cyclicNext C.length_pos prev))),
      D.edge (C.vertices prev)
        (C.vertices (cyclicNext C.length_pos prev))
        (C.next_ne prev) = some a →
      S.colour (point (C.vertices prev))
        (point (C.vertices (cyclicNext C.length_pos prev))) = some a) :
    CycleHom C := by
  refine ⟨fun p => point (C.vertices p), ?_⟩
  intro p a hEdge
  by_cases h0 : p = p0
  · subst p
    exact hFirst a hEdge
  · by_cases h1 : p = prev
    · subst p
      exact hPrev a hEdge
    · exact hOther p h0 h1 a hEdge

end CCO.RawExact
