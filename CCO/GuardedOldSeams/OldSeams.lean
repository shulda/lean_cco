import CCO.UnarySupport.TypedTerms

/-!
# Literal OLD unary-coordinate seams

All readouts and all transition equations below belong to the original
partial unary source.  A defined term is enough: totality, SAP, CCO and a
completion map are absent.  The inductive chain is finite, and its seam
is one actual OLD readout, not an equality of future target images.
-/

universe u v

namespace CCO.GuardedOldSeams

open UnarySupport UnarySupport.Structure

variable {L : Signature.{u}} {V : Type v}
variable (C : UnarySupport.Structure L V)

/-- A typed named OLD readout, with its actual defined source value. -/
structure OldReadout (A : Set V) (coordinate : L.Sorts) where
  input : L.Sorts
  root : V
  root_mem : root ∈ A
  root_sort : C.sort root = input
  term : Term L input coordinate
  value : V
  defined : value ∈ C.eval term root

theorem OldReadout.value_mem {A : Set V} {i : L.Sorts}
    (q : OldReadout C A i) (hA : C.IsClosed A) : q.value ∈ A :=
  C.eval_closed hA q.term q.root_mem q.defined

theorem OldReadout.value_sort {A : Set V} {i : L.Sorts}
    (q : OldReadout C A i) : C.sort q.value = i :=
  C.eval_sorted q.term q.root_sort q.defined

/-- Composition of existing typed unary syntax, with no new symbol. -/
def composeOldTerms {i j k : L.Sorts}
    (outer : Term L j k) (inner : Term L i j) : Term L i k :=
  match outer with
  | .var _ => inner
  | .func F tail => .func F (composeOldTerms tail inner)

theorem eval_composeOldTerms {i j k : L.Sorts}
    (outer : Term L j k) (inner : Term L i j) (x y : V) :
    y ∈ C.eval (composeOldTerms outer inner) x ↔
      ∃ z, z ∈ C.eval inner x ∧ y ∈ C.eval outer z := by
  induction outer generalizing y with
  | var =>
      constructor
      · intro h
        exact ⟨y, h, rfl⟩
      · rintro ⟨z, hz, hy⟩
        exact hy ▸ hz
  | func F outer ih =>
      constructor
      · rintro ⟨z, hz, hzy⟩
        obtain ⟨a, ha, haz⟩ := (ih z).mp hz
        exact ⟨a, ha, z, haz, hzy⟩
      · rintro ⟨a, ha, z, haz, hzy⟩
        exact ⟨z, (ih z).mpr ⟨a, ha, haz⟩, hzy⟩

/-- A macro side supplies its displayed OLD unary transition and the
literal source equality of its actual output with the next readout. -/
structure OldUnarySide {A : Set V} {i j : L.Sorts}
    (left : OldReadout C A i) (right : OldReadout C A j) where
  transition : Term L i j
  output : V
  defined : output ∈ C.eval transition left.value
  equation : output = right.value

theorem OldUnarySide.realizes {A : Set V} {i j : L.Sorts}
    {left : OldReadout C A i} {right : OldReadout C A j}
    (side : OldUnarySide C left right) :
    right.value ∈ C.eval side.transition left.value :=
  side.equation ▸ side.defined

/-- Two notations at the SAME quotient coordinate may be substituted
only when their equality is already literal in the OLD source. -/
def old_literal_seam {A : Set V} {i : L.Sorts}
    (left right : OldReadout C A i) (h : left.value = right.value) :
    OldUnarySide C left right where
  transition := .var i
  output := left.value
  defined := rfl
  equation := h

/-- A finite chain shares an actual intermediate OLD readout.  An
explicit old named connecting transition is simply another side. -/
inductive OldSeamChain (A : Set V) :
    {i j : L.Sorts} → OldReadout C A i → OldReadout C A j → Type (max u v)
  | nil {i : L.Sorts} (q : OldReadout C A i) : OldSeamChain A q q
  | cons {i j k : L.Sorts} {q : OldReadout C A i}
      {r : OldReadout C A j} {s : OldReadout C A k}
      (side : OldUnarySide C q r) (tail : OldSeamChain A r s) :
      OldSeamChain A q s

def OldSeamChain.term {A : Set V} {i j : L.Sorts}
    {left : OldReadout C A i} {right : OldReadout C A j}
    (chain : OldSeamChain C A left right) : Term L i j :=
  match chain with
  | .nil _ => .var _
  | .cons side tail => composeOldTerms tail.term side.transition

/-- C17: ordinary substitution in the source realizes the full composite. -/
theorem OldSeamChain.realizes {A : Set V} {i j : L.Sorts}
    {left : OldReadout C A i} {right : OldReadout C A j}
    (chain : OldSeamChain C A left right) :
    right.value ∈ C.eval chain.term left.value := by
  induction chain with
  | nil => rfl
  | cons side tail ih =>
      exact (eval_composeOldTerms C tail.term side.transition _ _).mpr
        ⟨_, side.realizes, ih⟩

/-- C15--C20/OSE: the composite's actual value is literally the last OLD
coordinate value and remains inside the functionally closed source. -/
theorem old_seam_telescope {A : Set V} (hA : C.IsClosed A)
    {i j : L.Sorts} {left : OldReadout C A i} {right : OldReadout C A j}
    (chain : OldSeamChain C A left right) {z : V}
    (hz : z ∈ C.eval chain.term left.value) :
    z = right.value ∧ z ∈ A := by
  have heq : z = right.value := C.eval_functional chain.term hz chain.realizes
  exact ⟨heq, heq ▸ OldReadout.value_mem C right hA⟩

/-- The finite chain of length zero is the literal identity term. -/
theorem old_seam_empty {A : Set V} {i : L.Sorts} (q : OldReadout C A i) :
    (OldSeamChain.nil q).term = (.var i : Term L i i) ∧
      q.value ∈ C.eval (OldSeamChain.nil q).term q.value :=
  ⟨rfl, rfl⟩

end CCO.GuardedOldSeams
