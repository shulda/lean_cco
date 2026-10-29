import CCO.UnarySupport.BoundaryLanguages

/-! Genuine binary operations, deliberately OUTSIDE the source signature.
These finite examples explain why the unary hypotheses cannot be dropped. -/
namespace CCO.UnarySupport.Boundaries.Binary

structure Diagram (V : Type) where
  op : V → V → Set V
  functional : ∀ x y z w, z ∈ op x y → w ∈ op x y → z = w

namespace Diagram
variable {V : Type}

def Total (C : Diagram V) : Prop := ∀ x y, (C.op x y).Nonempty
def Closed (C : Diagram V) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, C.op x y ⊆ S

structure FreeDecompositionOn (C : Diagram V) (S : Set V) where
  left : Set V
  right : Set V
  left_sub : left ⊆ S
  right_sub : right ⊆ S
  left_closed : C.Closed left
  right_closed : C.Closed right
  cover : left ∪ right = S
  left_proper : left ≠ S
  right_proper : right ≠ S
  graph_local : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ C.op x y,
    (x ∈ left ∧ y ∈ left ∧ z ∈ left) ∨ (x ∈ right ∧ y ∈ right ∧ z ∈ right)

def IrreducibleOn (C : Diagram V) (S : Set V) : Prop := IsEmpty (C.FreeDecompositionOn S)

def induce (C : Diagram V) (S : Set V) (_hS : C.Closed S) : Diagram S where
  op x y := {z | z.val ∈ C.op x.val y.val}
  functional x y z w hz hw := Subtype.ext (C.functional x.val y.val z.val w.val hz hw)

inductive Reach (C : Diagram V) (B : Set V) : V → Prop
  | generator (x) : x ∈ B → Reach C B x
  | operation (x y z) : Reach C B x → Reach C B y → z ∈ C.op x y → Reach C B z

def closure (C : Diagram V) (B : Set V) : Set V := {x | C.Reach B x}

theorem closure_minimal (C : Diagram V) {B S : Set V} (hS : C.Closed S) (hBS : B ⊆ S) :
    C.closure B ⊆ S := by
  intro x hx
  induction hx with
  | generator y hy => exact hBS hy
  | operation x y z hx hy hz ihx ihy => exact hS x ihx y ihy hz

end Diagram

def diagonal : Diagram Bool where
  op x y := if x = y then {x} else ∅
  functional x y z w hz hw := by split at hz <;> simp_all

theorem diagonal_closed (S : Set Bool) : diagonal.Closed S := by
  intro x hx y hy z hz
  simp only [diagonal] at hz
  split at hz
  · exact hz ▸ hx
  · exact False.elim hz

def diagonalFree : diagonal.FreeDecompositionOn Set.univ where
  left := {false}
  right := {true}
  left_sub := Set.subset_univ _
  right_sub := Set.subset_univ _
  left_closed := diagonal_closed _
  right_closed := diagonal_closed _
  cover := by ext x; cases x <;> simp
  left_proper h := by have ht : true ∈ ({false} : Set Bool) := h ▸ Set.mem_univ true; cases ht
  right_proper h := by have hf : false ∈ ({true} : Set Bool) := h ▸ Set.mem_univ false; cases hf
  graph_local := by
    intro x hx y hy z hz
    cases x <;> cases y <;> cases z <;> simp_all [diagonal]

theorem diagonal_irreducible_subsingleton (S : Set Bool) (h : diagonal.IrreducibleOn S) :
    S.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hfull : S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    cases x <;> cases y <;> cases z <;> simp_all
  rw [hfull] at h
  exact h.false diagonalFree

/-- Every ACTUAL irreducible induced diagram is a total singleton (or the
empty total diagram), while the whole two-point diagram has missing domains. -/
theorem diagonal_actual_irreducibles_total (S : Set Bool) (hS : diagonal.Closed S)
    (h : diagonal.IrreducibleOn S) : (diagonal.induce S hS).Total := by
  intro x y
  have he : x.val = y.val := diagonal_irreducible_subsingleton S h x.property y.property
  refine ⟨x, ?_⟩
  change x.val ∈ (if x.val = y.val then ({x.val} : Set Bool) else ∅)
  simp [he]

theorem diagonal_not_total : ¬ diagonal.Total := by
  intro h
  obtain ⟨z, hz⟩ := h false true
  simp [diagonal] at hz

def meetThree : Diagram (Fin 3) where
  op x y := {if x = y then x else 2}
  functional _x _y _z _w hz hw := hz.trans hw.symm

theorem meet_singleton_closed (x : Fin 3) : meetThree.Closed {x} := by
  intro a ha b hb z hz
  have ha' : a = x := ha
  have hb' : b = x := hb
  subst a
  subst b
  simpa [meetThree] using hz

theorem meet_pair_generates_bottom : (2 : Fin 3) ∈ meetThree.closure {0, 1} := by
  exact .operation 0 1 2 (.generator 0 (by simp)) (.generator 1 (by simp)) (by simp [meetThree])

theorem meet_singletons_omit_bottom :
    (2 : Fin 3) ∉ meetThree.closure {0} ∪ meetThree.closure {1} := by
  rintro (h | h)
  · have h' := meetThree.closure_minimal (meet_singleton_closed 0) (Set.Subset.refl _) h
    simp at h'
  · have h' := meetThree.closure_minimal (meet_singleton_closed 1) (Set.Subset.refl _) h
    simp at h'

theorem binary_scope_counterexamples :
    (∀ S (hS : diagonal.Closed S), diagonal.IrreducibleOn S → (diagonal.induce S hS).Total) ∧
    ¬ diagonal.Total ∧
    meetThree.closure ({0, 1} : Set (Fin 3)) ≠ meetThree.closure {0} ∪ meetThree.closure {1} := by
  refine ⟨diagonal_actual_irreducibles_total, diagonal_not_total, ?_⟩
  intro he
  exact meet_singletons_omit_bottom (he ▸ meet_pair_generates_bottom)

end CCO.UnarySupport.Boundaries.Binary
