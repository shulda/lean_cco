import CCO.Finite
import Lean.Elab.Tactic.Omega

/-!
# Finite serial cycles with one rigid anchor

Choose successive witnesses along the finite cycle. The final state lies in
the original singleton, so it is literally the initial real point. This small
lemma contains no homogeneity/CCO/SAP premise and does not assert any cycle
realization without the displayed seriality and actual singleton condition.
-/

universe u v w
namespace CCO.RealHull.Geometry

theorem serial_cycle_with_singleton {M : Type u} {n : ℕ} (hn : 0 < n)
    (R : Fin n → M → Prop) (E : Fin n → M → M → Prop) (a : M)
    (hzero : ∀ p, R ⟨0,hn⟩ p ↔ p = a)
    (hstep : ∀ i p, R i p → ∃ q, R (cyclicNext hn i) q ∧ E i p q) :
    ∃ p : Fin n → M, ∀ i, E i (p i) (p (cyclicNext hn i)) := by
  classical
  let idx : ℕ → Fin n := fun k => ⟨k % n, Nat.mod_lt _ hn⟩
  have idx_zero : idx 0 = ⟨0,hn⟩ := Fin.ext (Nat.zero_mod n)
  have idx_end : idx n = ⟨0,hn⟩ := Fin.ext (Nat.mod_self n)
  have idx_succ (k : ℕ) : idx (k+1) = cyclicNext hn (idx k) := by
    apply Fin.ext
    change (k+1)%n = (k%n+1)%n
    simp only [Nat.add_mod,Nat.mod_mod]
  let State (k : ℕ) := {p : M // R (idx k) p}
  let initial : State 0 := ⟨a, by rw [idx_zero]; exact (hzero a).mpr rfl⟩
  let advance (k : ℕ) (p : State k) : State (k+1) :=
    ⟨Classical.choose (hstep (idx k) p.val p.property), by
      rw [idx_succ]
      exact (Classical.choose_spec (hstep (idx k) p.val p.property)).1⟩
  let states : ∀ k, State k := fun k => Nat.rec initial advance k
  let point : ℕ → M := fun k => (states k).val
  have hedge (k : ℕ) : E (idx k) (point k) (point (k+1)) :=
    (Classical.choose_spec (hstep (idx k) (states k).val (states k).property)).2
  have close : point n = point 0 := by
    have hh : R (idx n) (point n) := (states n).property
    have hh' : R ⟨0,hn⟩ (point n) := by simpa only [idx_end] using hh
    exact (hzero _).mp hh'
  let points : Fin n → M := fun i => point i.val
  refine ⟨points, ?_⟩
  intro i
  have hi : idx i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hnext : points (cyclicNext hn i) = point (i.val+1) := by
    change point ((i.val+1)%n) = point (i.val+1)
    by_cases hlt : i.val+1 < n
    · rw [Nat.mod_eq_of_lt hlt]
    · have heq : i.val+1 = n := by omega
      rw [heq,Nat.mod_self]
      exact close.symm
  have hh := hedge i.val
  rw [hi] at hh
  simpa only [hnext] using hh

/-- Source-facing actual CycleHom readout. Every optional specified edge is
preserved in its original typed palette, including the closing edge.
-/
theorem cycleHom_of_singleton_serial {M : Type u}
    (S : AtomicSource.{0,u,w} Unit (fun _ => M)) {V : Type v}
    (D : PartialDiagram S V) (C : SimpleCycle D)
    (R : V → M → Prop) (a : M)
    (hzero : ∀ p, R (C.vertices ⟨0,C.length_pos⟩) p ↔ p = a)
    (hstep : ∀ (i : Fin C.length) p, R (C.vertices i) p →
      ∃ q, R (C.vertices (cyclicNext C.length_pos i)) q ∧
        ∀ (c : S.Atom (D.vertexSort (C.vertices i))
          (D.vertexSort (C.vertices (cyclicNext C.length_pos i)))),
          D.edge (C.vertices i) (C.vertices (cyclicNext C.length_pos i)) (C.next_ne i) = some c →
          S.colour (i := D.vertexSort (C.vertices i))
            (j := D.vertexSort (C.vertices (cyclicNext C.length_pos i))) p q = some c) :
    CycleHom C := by
  let E (i : Fin C.length) (p q : M) : Prop :=
    ∀ (c : S.Atom (D.vertexSort (C.vertices i))
      (D.vertexSort (C.vertices (cyclicNext C.length_pos i)))),
      D.edge (C.vertices i) (C.vertices (cyclicNext C.length_pos i)) (C.next_ne i) = some c →
      S.colour (i := D.vertexSort (C.vertices i))
        (j := D.vertexSort (C.vertices (cyclicNext C.length_pos i))) p q = some c
  obtain ⟨p,hp⟩ := serial_cycle_with_singleton C.length_pos
    (fun i => R (C.vertices i)) E a hzero hstep
  exact ⟨p,hp⟩

end CCO.RealHull.Geometry
