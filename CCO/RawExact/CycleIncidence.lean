import CCO.RawExact.CyclicIndex
import CCO.Finite

/-!
# Finite cycle root incidences

An injectively enumerated simple cycle traverses any chosen vertex at most
once. Its outgoing edge is therefore determined by the unique root index,
and its incoming edge is determined by the unique cyclic predecessor.
-/

universe u v w z

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} {D : PartialDiagram S V}

theorem cyclicNext_surjective {n : Nat} (hn : 0 < n) :
    Function.Surjective (cyclicNext hn) :=
  (Finite.injective_iff_surjective).mp (cyclicNext_injective hn)

theorem cycle_root_incidences
    (C : SimpleCycle D) (r : V) (p0 : Fin C.length)
    (hp0 : C.vertices p0 = r) :
    ∃ prev : Fin C.length,
      cyclicNext C.length_pos prev = p0 ∧
      (∀ p, C.vertices p = r → p = p0) ∧
      (∀ p, C.vertices (cyclicNext C.length_pos p) = r → p = prev) := by
  obtain ⟨prev, hprev⟩ :=
    cyclicNext_surjective C.length_pos p0
  refine ⟨prev, hprev, ?_, ?_⟩
  · intro p hp
    exact C.vertices.injective (hp.trans hp0.symm)
  · intro p hp
    apply cyclicNext_injective C.length_pos
    exact (C.vertices.injective (hp.trans hp0.symm)).trans hprev.symm

end CCO.RawExact
