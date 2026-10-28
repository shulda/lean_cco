import CCO.StrongExact.CycleIndexRotation

/-!
# Reverse an actual specified simple cycle without changing its semantics

Finite index reversal reverses every original edge with its actual typed
converse. The new cycle has a homomorphism exactly when the old one does.
Together with rotation, this lets a cut edge be given a chosen orientation
before extracting its genuine simple old path. No arbitrary walk reversal
is assumed.
-/

universe u v w z
namespace CCO

/-- Finite ordinal reversal as an actual involutive equivalence. -/
def cycleReversal {n : Nat} : Fin n ≃ Fin n where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

/-- Reversing the successor edge yields the predecessor edge, including
both ordinal wraps. The displayed equation avoids implicit reindexing. -/
theorem cyclicNext_rev_next {n : Nat} (hn : 0 < n) (p : Fin n) :
    cyclicNext hn (cyclicNext hn p).rev = p.rev := by
  apply Fin.ext
  change (n - (((p.val + 1) % n) + 1) + 1) % n = n - (p.val + 1)
  by_cases hLast : p.val + 1 = n
  · rw [hLast,Nat.mod_self]
    simp only [Nat.zero_add,Nat.sub_self]
    have hLength : n - 1 + 1 = n := by omega
    rw [hLength,Nat.mod_self]
  · have hLt : p.val + 1 < n := by omega
    rw [Nat.mod_eq_of_lt hLt]
    have hStep : n - (p.val + 1 + 1) + 1 = n - (p.val + 1) := by omega
    rw [hStep,Nat.mod_eq_of_lt (by omega)]

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable {D : PartialDiagram S V}

private def reverseSpecifiedPair (D : PartialDiagram S V) (x y : V) : Prop :=
  ∀ hxy : x ≠ y, ∃ a : S.Atom (D.vertexSort x) (D.vertexSort y),
    D.edge x y hxy = some a

private def reversePointPreserves (C : SimpleCycle D)
    (point : ∀ q : Fin C.length, X (D.vertexSort (C.vertices q)))
    (p q : Fin C.length) : Prop :=
  ∀ (hne : C.vertices p ≠ C.vertices q)
    (a : S.Atom (D.vertexSort (C.vertices p)) (D.vertexSort (C.vertices q))),
    D.edge (C.vertices p) (C.vertices q) hne = some a →
      S.colour (point p) (point q) = some a

private theorem reversePointPreserves_swap (C : SimpleCycle D)
    (point : ∀ q : Fin C.length, X (D.vertexSort (C.vertices q)))
    {p q : Fin C.length} (h : reversePointPreserves C point p q) :
    reversePointPreserves C point q p := by
  intro hne a ha
  exact (S.colour_swap (point q) (point p) a).mpr
    (h hne.symm (S.conv a)
      ((D.edge_reverse (C.vertices q) (C.vertices p) hne a).mp ha))

/-- The genuine old cycle with all traversal directions reversed. -/
noncomputable def SimpleCycle.reverse (C : SimpleCycle D) : SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := ⟨(fun p => C.vertices p.rev), by
    intro p q h
    have hh := congrArg Fin.rev (C.vertices.injective h)
    simpa only [Fin.rev_rev] using hh⟩
  next_ne p := by
    have h := (C.next_ne (cyclicNext C.length_pos p).rev).symm
    rw [cyclicNext_rev_next] at h
    exact h
  specified p := by
    have hForward : reverseSpecifiedPair D
        (C.vertices (cyclicNext C.length_pos p).rev)
        (C.vertices (cyclicNext C.length_pos (cyclicNext C.length_pos p).rev)) := by
      intro _hne
      exact C.specified _
    rw [cyclicNext_rev_next] at hForward
    have hReverse : reverseSpecifiedPair D (C.vertices p.rev)
        (C.vertices (cyclicNext C.length_pos p).rev) := by
      intro hne
      obtain ⟨a,ha⟩ := hForward hne.symm
      exact ⟨S.conv a,(D.edge_reverse _ _ hne.symm a).mp ha⟩
    exact hReverse _

theorem SimpleCycle.reverse_vertices (C : SimpleCycle D) (p : Fin C.length) :
    C.reverse.vertices p = C.vertices p.rev := rfl

/-- A chosen edge of the old cycle occurs in the new cycle in precisely
the reverse direction, at this explicit finite index. -/
theorem SimpleCycle.reverse_edge_endpoints (C : SimpleCycle D) (cut : Fin C.length) :
    C.reverse.vertices (cyclicNext C.length_pos cut).rev =
      C.vertices (cyclicNext C.length_pos cut) ∧
    C.reverse.vertices
      (cyclicNext C.length_pos (cyclicNext C.length_pos cut).rev) = C.vertices cut := by
  constructor
  · change C.vertices (cyclicNext C.length_pos cut).rev.rev = _
    rw [Fin.rev_rev]
  · change C.vertices (cyclicNext C.length_pos (cyclicNext C.length_pos cut).rev).rev = _
    rw [cyclicNext_rev_next,Fin.rev_rev]

/-- Actual original-colour homomorphisms are invariant under reversal;
each reversed atomic edge uses BOTH the diagram and source converse. -/
theorem SimpleCycle.cycleHom_reverse_iff (C : SimpleCycle D) :
    CycleHom C.reverse ↔ CycleHom C := by
  constructor
  · rintro ⟨reversed,hReversed⟩
    let P (q : Fin C.length) := X (D.vertexSort (C.vertices q))
    let point : ∀ q : Fin C.length, P q := Equiv.piCongrLeft P cycleReversal reversed
    have hRead (p : Fin C.length) : point p.rev = reversed p :=
      Equiv.piCongrLeft_apply_apply P cycleReversal reversed p
    have hNew (p : Fin C.length) :
        reversePointPreserves C point p.rev (cyclicNext C.length_pos p).rev := by
      intro _hne a ha
      rw [hRead,hRead]
      exact hReversed p a ha
    refine ⟨point,?_⟩
    intro q
    have hBack := hNew (cyclicNext C.length_pos q).rev
    simp only [Fin.rev_rev,cyclicNext_rev_next] at hBack
    exact reversePointPreserves_swap C point hBack (C.next_ne q)
  · rintro ⟨point,hPoint⟩
    refine ⟨fun p => point p.rev,?_⟩
    intro p
    change Fin C.length at p
    have hOld : reversePointPreserves C point (cyclicNext C.length_pos p).rev
        (cyclicNext C.length_pos (cyclicNext C.length_pos p).rev) := by
      intro _hne
      exact hPoint _
    rw [cyclicNext_rev_next] at hOld
    exact reversePointPreserves_swap C point hOld (C.reverse.next_ne p)

end CCO
