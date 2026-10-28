import CCO.StrongExact.ThetaCycleIndexInjectivity
import CCO.StrongExact.ThetaCycleAdvanceShift
import CCO.StrongExact.ThetaCycleAdvanceAddition
import Mathlib.Logic.Equiv.Basic
import Lean.Elab.Tactic.Omega

/-!
# Literal finite-cycle rotation and homomorphism reindexing

Rotate any finite nonempty cyclic ordinal to a chosen start. The actual
cyclic successor commutes with this permutation, including its wrap. For
simple cycles this changes only the indexing; all original typed vertices,
edges, and cycle-homomorphism obligations remain exactly the same.
-/

universe u v w z
namespace CCO
open StrongExact

/-- The actual cyclic-successor permutation with a chosen initial index. -/
noncomputable def cycleRotation {n : Nat} (hn : 0 < n) (start : Fin n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun p => thetaCycleAdvance hn start p.val)
    ⟨by
      intro p q h
      exact Fin.ext (thetaCycleAdvance_injective_lt hn start p.val q.val p.isLt q.isLt h),
     by
      intro q
      obtain ⟨m,hm,he⟩ := thetaCycleAdvance_reaches hn start q
      exact ⟨⟨m,hm⟩,he⟩⟩

theorem cycleRotation_apply {n : Nat} (hn : 0 < n) (start p : Fin n) :
    cycleRotation hn start p = thetaCycleAdvance hn start p.val := rfl

/-- Rotation commutes with the ACTUAL cyclic successor, including
both the ordinal wrap and a chosen nonzero starting index. -/
theorem cycleRotation_next {n : Nat} (hn : 0 < n) (start p : Fin n) :
    cycleRotation hn start (cyclicNext hn p) =
      cyclicNext hn (cycleRotation hn start p) := by
  apply Fin.ext
  change (thetaCycleAdvance hn start ((p.val + 1) % n)).val =
    ((thetaCycleAdvance hn start p.val).val + 1) % n
  rw [thetaCycleAdvance_val,thetaCycleAdvance_val,Nat.add_mod_mod,Nat.mod_add_mod]
  congr 1

@[simp] theorem cycleRotation_zero {n : Nat} (hn : 0 < n) (start : Fin n) :
    cycleRotation hn start ⟨0,hn⟩ = start := rfl

/-- Starting just AFTER a cut edge makes its source the last index;
the old cut edge is therefore exactly the closing last-to-zero edge. -/
theorem cycleRotation_after_last {n : Nat} (hn : 0 < n) (cut : Fin n) :
    cycleRotation hn (cyclicNext hn cut) ⟨n - 1,by omega⟩ = cut := by
  rw [cycleRotation_apply,thetaCycleAdvance_from_next]
  have hLength : n - 1 + 1 = n := by omega
  rw [hLength]
  apply Fin.ext
  rw [thetaCycleAdvance_val]
  simp [Nat.mod_eq_of_lt cut.isLt]

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable {D : PartialDiagram S V}

private def cycleSpecifiedPair (D : PartialDiagram S V) (x y : V) : Prop :=
  ∀ hxy : x ≠ y, ∃ a : S.Atom (D.vertexSort x) (D.vertexSort y),
    D.edge x y hxy = some a

private def cyclePointPreserves (C : SimpleCycle D)
    (point : ∀ q : Fin C.length, X (D.vertexSort (C.vertices q)))
    (p q : Fin C.length) : Prop :=
  ∀ (hne : C.vertices p ≠ C.vertices q)
    (a : S.Atom (D.vertexSort (C.vertices p)) (D.vertexSort (C.vertices q))),
    D.edge (C.vertices p) (C.vertices q) hne = some a →
      S.colour (point p) (point q) = some a

/-- Rotate a genuine specified simple cycle, keeping all original
vertices and old typed atomic constraints. -/
noncomputable def SimpleCycle.rotate (C : SimpleCycle D) (start : Fin C.length) :
    SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := ⟨(fun p => C.vertices (cycleRotation C.length_pos start p)),
    fun _ _ h => (cycleRotation C.length_pos start).injective (C.vertices.injective h)⟩
  next_ne p := by
    change C.vertices (cycleRotation C.length_pos start p) ≠
      C.vertices (cycleRotation C.length_pos start (cyclicNext C.length_pos p))
    rw [cycleRotation_next]
    exact C.next_ne _
  specified p := by
    have h : cycleSpecifiedPair D
        (C.vertices (cycleRotation C.length_pos start p))
        (C.vertices (cyclicNext C.length_pos (cycleRotation C.length_pos start p))) := by
      intro _hne
      exact C.specified _
    have hRot : cycleSpecifiedPair D
        (C.vertices (cycleRotation C.length_pos start p))
        (C.vertices (cycleRotation C.length_pos start (cyclicNext C.length_pos p))) := by
      rw [cycleRotation_next]
      exact h
    exact hRot _

theorem SimpleCycle.rotate_vertices (C : SimpleCycle D) (start p : Fin C.length) :
    (C.rotate start).vertices p = C.vertices (cycleRotation C.length_pos start p) := rfl

@[simp] theorem SimpleCycle.rotate_zero_vertices (C : SimpleCycle D)
    (start : Fin C.length) :
    (C.rotate start).vertices ⟨0,C.length_pos⟩ = C.vertices start := rfl

/-- A cut cycle is rotated so its chosen edge is literally the closing
last-to-first edge, without changing any original vertex or sort. -/
theorem SimpleCycle.rotate_after_cut_last (C : SimpleCycle D) (cut : Fin C.length) :
    (C.rotate (cyclicNext C.length_pos cut)).vertices
      ⟨C.length - 1,by
        change C.length - 1 < C.length
        have hPos := C.length_pos
        omega⟩ = C.vertices cut :=
  congrArg C.vertices (cycleRotation_after_last C.length_pos cut)

/-- A cyclic reindexing neither creates nor removes an original-colour
cycle homomorphism. Dependent point families are transported by an actual
finite equivalence, rather than identifying their named sorts. -/
theorem SimpleCycle.cycleHom_rotate_iff (C : SimpleCycle D) (start : Fin C.length) :
    CycleHom (C.rotate start) ↔ CycleHom C := by
  let r := cycleRotation C.length_pos start
  constructor
  · rintro ⟨rotated,hRotated⟩
    let P (q : Fin C.length) := X (D.vertexSort (C.vertices q))
    let point : ∀ q : Fin C.length, P q := Equiv.piCongrLeft P r rotated
    have hRead (p : Fin C.length) : point (r p) = rotated p :=
      Equiv.piCongrLeft_apply_apply P r rotated p
    refine ⟨point,?_⟩
    intro q
    obtain ⟨p,hp⟩ := r.surjective q
    subst q
    have hStep : cyclePointPreserves C point (r p) (r (cyclicNext C.length_pos p)) := by
      intro _hne a ha
      rw [hRead,hRead]
      exact hRotated p a ha
    have hNext : r (cyclicNext C.length_pos p) = cyclicNext C.length_pos (r p) :=
      cycleRotation_next C.length_pos start p
    have hOriginal : cyclePointPreserves C point (r p) (cyclicNext C.length_pos (r p)) := by
      rw [← hNext]
      exact hStep
    exact hOriginal (C.next_ne (r p))

  · rintro ⟨point,hPoint⟩
    refine ⟨fun p => point (r p),?_⟩
    intro p
    have hStep : cyclePointPreserves C point (r p) (cyclicNext C.length_pos (r p)) := by
      intro _hne
      exact hPoint (r p)
    have hNext : r (cyclicNext C.length_pos p) = cyclicNext C.length_pos (r p) :=
      cycleRotation_next C.length_pos start p
    have hRot : cyclePointPreserves C point (r p) (r (cyclicNext C.length_pos p)) := by
      rw [hNext]
      exact hStep
    exact hRot ((C.rotate start).next_ne p)

end CCO
