import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Embedding.Basic

/-! Arbitrary typed diversity palettes. Neither the sorts nor the atoms are
assumed finite or realized in an ambient structure. -/
universe u v
namespace CCO.RelationalCompletion.Atomic

structure Palette where
  Sorts : Type u
  Atom : Type v
  src : Atom → Sorts
  tgt : Atom → Sorts
  conv : Atom → Atom
  conv_conv : ∀ a, conv (conv a) = a
  src_conv : ∀ a, src (conv a) = tgt a
  tgt_conv : ∀ a, tgt (conv a) = src a

/-- The only predicates are complete exclusive vertex tags and diversity atoms.
Logical equality is separate from diversity and every diversity diagonal is false. -/
structure Diagram (P : Palette.{u,v}) (n : Nat) where
  tag : Fin n → P.Sorts
  edge : Fin n → Fin n → Option P.Atom
  edge_self : ∀ x, edge x x = none
  edge_reverse : ∀ x y, edge y x = (edge x y).map P.conv
  typed : ∀ x y a, edge x y = some a → P.src a = tag x ∧ P.tgt a = tag y

structure Model (P : Palette.{u,v}) where
  size : Nat
  diagram : Diagram P size
  complete : ∀ x y, x ≠ y → ∃ a, diagram.edge x y = some a

abbrev Model.tag {P : Palette} (A : Model P) := A.diagram.tag
abbrev Model.edge {P : Palette} (A : Model P) := A.diagram.edge

namespace Model
variable {P : Palette.{u,v}}

theorem ne_of_edge {A : Model P} {x y : Fin A.size} {a : P.Atom}
    (h : A.edge x y = some a) : x ≠ y := by
  intro he; subst y
  change A.diagram.edge x x = some a at h
  rw [A.diagram.edge_self] at h
  contradiction

abbrev pullback (A : Model P) {n : Nat} (e : Fin n ↪ Fin A.size) : Model P where
  size := n
  diagram := {
    tag := fun x => A.tag (e x)
    edge := fun x y => A.edge (e x) (e y)
    edge_self := fun x => A.diagram.edge_self (e x)
    edge_reverse := fun x y => A.diagram.edge_reverse (e x) (e y)
    typed := fun x y a h => A.diagram.typed (e x) (e y) a h }
  complete := fun x y h => A.complete (e x) (e y) (e.injective.ne h)

@[simp] theorem edge_pullback (A : Model P) {n} (e : Fin n ↪ Fin A.size) (x y) :
    (A.pullback e).edge x y = A.edge (e x) (e y) := rfl

/-- The full atomic binary type, including both complete unary tags. -/
def colour (A : Model P) (x y : Fin A.size) :
    Σ _i : P.Sorts, Σ _j : P.Sorts, Option P.Atom :=
  ⟨A.tag x, A.tag y, A.edge x y⟩

def reverseTagged (P : Palette) (c : Σ _i : P.Sorts, Σ _j : P.Sorts, Option P.Atom) :
    Σ _i : P.Sorts, Σ _j : P.Sorts, Option P.Atom := ⟨c.2.1, c.1, c.2.2.map P.conv⟩

theorem colour_self (A : Model P) (x) :
    A.colour x x = ⟨A.tag x, A.tag x, none⟩ := by
  simp [colour, A.diagram.edge_self]

theorem colour_reverse (A : Model P) (x y) :
    A.colour y x = reverseTagged P (A.colour x y) := by
  change (⟨A.tag y, A.tag x, A.diagram.edge y x⟩ : Σ _i : P.Sorts, Σ _j : P.Sorts, Option P.Atom) = _
  rw [A.diagram.edge_reverse x y]
  rfl

theorem colour_fst (A : Model P) (x y) : (A.colour x y).1 = A.tag x := rfl

theorem colour_snd_fst (A : Model P) (x y) : (A.colour x y).2.1 = A.tag y := rfl

theorem ne_of_colour_some (A : Model P) {i j : P.Sorts} {a : P.Atom}
    {x y : Fin A.size} (h : A.colour x y = ⟨i, j, some a⟩) : x ≠ y := by
  apply A.ne_of_edge
  exact congrArg (fun c : Σ _i : P.Sorts, Σ _j : P.Sorts, Option P.Atom => c.2.2) h

theorem colour_pullback (A : Model P) {n} (e : Fin n ↪ Fin A.size) (x y) :
    (A.pullback e).colour x y = A.colour (e x) (e y) := rfl

end Model

structure Embedding {P : Palette.{u,v}} (A B : Model P) where
  vertex : Fin A.size ↪ Fin B.size
  tag_eq : ∀ x, B.tag (vertex x) = A.tag x
  edge_eq : ∀ x y, B.edge (vertex x) (vertex y) = A.edge x y

structure Hom {P : Palette.{u,v}} {n : Nat} (D : Diagram P n) (B : Model P) where
  vertex : Fin n → Fin B.size
  tag_eq : ∀ x, B.tag (vertex x) = D.tag x
  edge_eq : ∀ x y a, D.edge x y = some a → B.edge (vertex x) (vertex y) = some a

theorem Embedding.preserves_colour {P : Palette} {A B : Model P} (e : Embedding A B) (x y) :
    B.colour (e.vertex x) (e.vertex y) = A.colour x y := by
  simp only [Model.colour, e.tag_eq, e.edge_eq]

/-- On complete inputs, preserving positive atoms forces both injectivity and
full reflection: there is exactly one atom on every distinct ordered pair. -/
def Hom.toEmbedding {P : Palette.{u,v}} {A B : Model P}
    (h : Hom A.diagram B) : Embedding A B := by
  have hinj : Function.Injective h.vertex := by
    intro x y he
    by_contra hn
    obtain ⟨a, ha⟩ := A.complete x y hn
    exact B.ne_of_edge (h.edge_eq x y a ha) he
  refine { vertex := ⟨h.vertex, hinj⟩, tag_eq := h.tag_eq, edge_eq := ?_ }
  intro x y
  change B.diagram.edge (h.vertex x) (h.vertex y) = A.diagram.edge x y
  by_cases he : x = y
  · subst y; rw [A.diagram.edge_self, B.diagram.edge_self]
  · obtain ⟨a, ha⟩ := A.complete x y he
    rw [ha]; exact h.edge_eq x y a ha

end CCO.RelationalCompletion.Atomic
