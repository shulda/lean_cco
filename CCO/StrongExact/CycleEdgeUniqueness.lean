import CCO.StrongExact.CycleIndexRotation

/-! A genuine simple cycle has no repeated unordered edge or fictitious two-cycle. -/

universe u v w z
namespace CCO.SimpleCycle
open StrongExact
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable {D : PartialDiagram S V}

theorem two_next_ne (C : SimpleCycle D) (q : Fin C.length) :
    cyclicNext C.length_pos (cyclicNext C.length_pos q) ≠ q := by
  intro h
  have hAdvance : thetaCycleAdvance C.length_pos q 2 =
      thetaCycleAdvance C.length_pos q 0 := h
  have hTwo : 2 < C.length := by
    have hLength := C.length_ge_three
    omega
  have hBad := thetaCycleAdvance_injective_lt C.length_pos q 2 0
    hTwo C.length_pos hAdvance
  omega

/-- Every unordered formal edge of a genuine simple cycle occurs at
exactly one cyclic index, including the wrap edge. The length≥3 gate
rules out the reversed two-step return. -/
theorem unordered_edge_unique (C : SimpleCycle D) (p q : Fin C.length)
    (h :
      (C.vertices p = C.vertices q ∧
        C.vertices (cyclicNext C.length_pos p) = C.vertices (cyclicNext C.length_pos q)) ∨
      (C.vertices p = C.vertices (cyclicNext C.length_pos q) ∧
        C.vertices (cyclicNext C.length_pos p) = C.vertices q)) : p = q := by
  rcases h with hForward | hReverse
  · exact C.vertices.injective hForward.1
  · have hp : p = cyclicNext C.length_pos q := C.vertices.injective hReverse.1
    have hNext : cyclicNext C.length_pos p = q := C.vertices.injective hReverse.2
    have hReturn : cyclicNext C.length_pos (cyclicNext C.length_pos q) = q := by
      rw [← hp]
      exact hNext
    exact False.elim (C.two_next_ne q hReturn)

end CCO.SimpleCycle
