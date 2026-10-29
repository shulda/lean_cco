import Mathlib.Data.Bool.Basic

/-! Explicit finite failures of weakened diagram premises. These are
set-diagram controls, with no claim of CCO, exactness, packet closure or EPPA. -/

namespace CCO.Owners.Master.Diagram.Controls

/-- Both projections are onto although one corner of the full product
over the singleton owner has been removed. -/
def MissingCorner := {x : Bool × Bool // ¬ (x.1 = true ∧ x.2 = true)}

def cornerFirst (x : MissingCorner) : Bool := x.val.1
def cornerSecond (x : MissingCorner) : Bool := x.val.2

theorem corner_first_onto : Function.Surjective cornerFirst := by
  intro b
  exact ⟨⟨(b,false),by simp⟩,rfl⟩

theorem corner_second_onto : Function.Surjective cornerSecond := by
  intro b
  exact ⟨⟨(false,b),by simp⟩,rfl⟩

theorem corner_owner_compatible (x y : Bool) :
    (fun _ : Bool => ()) x = (fun _ : Bool => ()) y := rfl

theorem corner_missing_compatible_tuple :
    ¬ ∃ x : MissingCorner, cornerFirst x = true ∧ cornerSecond x = true := by
  rintro ⟨x,hx,hy⟩
  exact x.property ⟨hx,hy⟩

theorem corner_coordinate_map_not_onto :
    ¬ Function.Surjective (fun x : MissingCorner => (cornerFirst x,cornerSecond x)) := by
  intro h
  obtain ⟨x,hx⟩ := h (true,true)
  apply corner_missing_compatible_tuple
  exact ⟨x,congrArg Prod.fst hx,congrArg Prod.snd hx⟩

/-- Every two-coordinate marginal of the sparse parity shadow is full;
its three-coordinate product still contains an unrealized compatible tuple. -/
def EvenTriple := {x : Bool × Bool × Bool // x.1.xor (x.2.1.xor x.2.2) = false}

def pair12 (x : EvenTriple) : Bool × Bool := (x.val.1,x.val.2.1)
def pair13 (x : EvenTriple) : Bool × Bool := (x.val.1,x.val.2.2)
def pair23 (x : EvenTriple) : Bool × Bool := (x.val.2.1,x.val.2.2)

theorem parity_pair12_onto : Function.Surjective pair12 := by
  rintro ⟨a,b⟩
  refine ⟨⟨(a,b,a.xor b),?_⟩,rfl⟩
  cases a <;> cases b <;> decide

theorem parity_pair13_onto : Function.Surjective pair13 := by
  rintro ⟨a,c⟩
  refine ⟨⟨(a,a.xor c,c),?_⟩,rfl⟩
  cases a <;> cases c <;> decide

theorem parity_pair23_onto : Function.Surjective pair23 := by
  rintro ⟨b,c⟩
  refine ⟨⟨(b.xor c,b,c),?_⟩,rfl⟩
  cases b <;> cases c <;> decide

theorem parity_missing_global_tuple :
    ¬ ∃ x : EvenTriple, x.val = (true,false,false) := by
  rintro ⟨x,hx⟩
  have h := x.property
  rw [hx] at h
  contradiction

/-- The empty tuple space is a singleton. A nonsingleton empty object
therefore violates the uniqueness half of the empty-family CRT. -/
def emptyCoordinates (_ : Bool) : Fin 0 → Bool := Fin.elim0

theorem empty_coordinate_map_not_injective : ¬ Function.Injective emptyCoordinates := by
  intro h
  have he : emptyCoordinates false = emptyCoordinates true := rfl
  have hfalse : false = true := h he
  contradiction

end CCO.Owners.Master.Diagram.Controls
