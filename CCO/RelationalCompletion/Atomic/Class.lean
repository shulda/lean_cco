import CCO.RelationalCompletion.Atomic.Palette
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! Hereditary atomic classes, ordinary amalgamation, and the exact locally
allowed semantic homomorphic CCO input. Off-base coincidences are permitted. -/
universe u v
namespace CCO.RelationalCompletion.Atomic
variable {P : Palette.{u,v}}

def Embedding.trans {A B C : Model P} (e : Embedding A B) (f : Embedding B C) :
    Embedding A C where
  vertex := e.vertex.trans f.vertex
  tag_eq x := (f.tag_eq (e.vertex x)).trans (e.tag_eq x)
  edge_eq x y := (f.edge_eq (e.vertex x) (e.vertex y)).trans (e.edge_eq x y)

def Model.pullbackEmbedding (A : Model P) {n} (e : Fin n ↪ Fin A.size) :
    Embedding (A.pullback e) A where
  vertex := e
  tag_eq _ := rfl
  edge_eq _ _ := rfl

def Hereditary (K : Model P → Prop) : Prop :=
  ∀ {A B : Model P}, Nonempty (Embedding A B) → K B → K A

def AP (K : Model P → Prop) : Prop :=
  ∀ (C A B : Model P), K C → K A → K B →
    ∀ (left : Embedding C A) (right : Embedding C B),
      ∃ T : Model P, K T ∧ ∃ (l : Embedding A T) (r : Embedding B T),
        ∀ x, l.vertex (left.vertex x) = r.vertex (right.vertex x)

def SmallSubmodels (K : Model P → Prop) (A : Model P) : Prop :=
  ∀ {n : Nat} (e : Fin n ↪ Fin A.size), n ≤ 3 → K (A.pullback e)

/-- Local allowedness is checked only for vertex types and specified pairs;
unrecorded pairs impose no simultaneous-realization requirement. -/
def LocalAllowed (K : Model P → Prop) {n} (D : Diagram P n) : Prop :=
  (∀ x, ∃ B : Model P, K B ∧ ∃ b, B.tag b = D.tag x) ∧
  (∀ x y a, D.edge x y = some a →
    ∃ B : Model P, K B ∧ ∃ b c,
      B.tag b = D.tag x ∧ B.tag c = D.tag y ∧ B.edge b c = some a)

def cyclicNext {n : Nat} (hn : 0 < n) (p : Fin n) : Fin n :=
  ⟨(p.val + 1) % n, Nat.mod_lt _ hn⟩

structure SimpleCycle {n} (D : Diagram P n) where
  length : Nat
  length_ge_three : 3 ≤ length
  vertices : Fin length ↪ Fin n
  specified : ∀ p, ∃ a, D.edge (vertices p)
    (vertices (cyclicNext (by omega) p)) = some a

def CycleHomInto {n} {D : Diagram P n} (C : SimpleCycle D) (B : Model P) : Prop :=
  ∃ point : Fin C.length → Fin B.size,
    (∀ p, B.tag (point p) = D.tag (C.vertices p)) ∧
    ∀ p a, D.edge (C.vertices p)
      (C.vertices (cyclicNext (by have := C.length_ge_three; omega) p)) = some a →
      B.edge (point p) (point (cyclicNext (by have := C.length_ge_three; omega) p)) = some a

/-- The original semantic CCO premise has an explicit local-allowedness gate.
It does not directly assert completeness, inducedness, or triangle fullness. -/
def SemanticCCO (K : Model P → Prop) : Prop :=
  ∀ {n : Nat} (D : Diagram P n), LocalAllowed K D →
    (∀ C : SimpleCycle D, ∃ B : Model P, K B ∧ CycleHomInto C B) →
      ∃ B : Model P, K B ∧ Nonempty (Hom D B)

/-- Actual small submodels include the complete unary and specified-pair data. -/
theorem localAllowed_of_small (K : Model P → Prop) (A : Model P)
    (small : SmallSubmodels K A) : LocalAllowed K A.diagram := by
  constructor
  · intro x
    let e : Fin 1 ↪ Fin A.size := ⟨fun _ => x, by intro a b h; exact Subsingleton.elim _ _⟩
    exact ⟨A.pullback e, small e (by decide), 0, rfl⟩
  · intro x y a ha
    have hxy := A.ne_of_edge ha
    let e : Fin 2 ↪ Fin A.size := {
      toFun := fun p => if p.val = 0 then x else y
      inj' := by intro p q h; fin_cases p <;> fin_cases q <;> simp_all }
    exact ⟨A.pullback e, small e (by decide), 0, 1, rfl, rfl, ha⟩

end CCO.RelationalCompletion.Atomic
