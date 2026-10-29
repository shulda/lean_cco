import CCO.ProfileHelly.Embeddings
import Mathlib.Data.Fintype.Sum

/-! A genuine finite pushout of FULL induced complete factors. Exactly
the common base is identified; all other cross-pairs remain holes. -/
universe u v a b c
namespace CCO.ProfileHelly
variable {ι : Type u} {T : Table.{u,v} ι}
variable {A : Type a} {L : Type b} {R : Type c}
variable {sortA : A → ι} {sortL : L → ι} {sortR : R → ι}

structure FreeAmalgam (B : CompleteNetwork T sortA) (C : CompleteNetwork T sortL)
    (D : CompleteNetwork T sortR) (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) where
  Carrier : Type (max a b c)
  finiteCarrier : Finite Carrier
  sort : Carrier → ι
  network : Network T sort
  left : Network.Embedding C.toNetwork network
  right : Network.Embedding D.toNetwork network
  commutes : ∀ x, left.point (f.point x) = right.point (g.point x)
  intersection : ∀ x y, left.point x = right.point y ↔ ∃ z, f.point z = x ∧ g.point z = y
  covered : ∀ x, (∃ y, left.point y = x) ∨ (∃ z, right.point z = x)
  edge_factor : ∀ x y, network.graph.Adj x y →
    (∃ s t, left.point s = x ∧ left.point t = y) ∨
      (∃ s t, right.point s = x ∧ right.point t = y)

namespace FreeAmalgamConstruction
variable {B : CompleteNetwork T sortA} {C : CompleteNetwork T sortL} {D : CompleteNetwork T sortR}

abbrev Carrier (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) : Type (max a b c) :=
  ULift.{a} (L ⊕ {r : R // r ∉ Set.range g.point})

def leftPoint (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (l : L) : Carrier f g := ⟨Sum.inl l⟩

noncomputable def rightPoint (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (r : R) : Carrier f g := by
  classical
  exact ⟨if h : r ∈ Set.range g.point then Sum.inl (f.point (Classical.choose h))
    else Sum.inr ⟨r,h⟩⟩

def leftProjection (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x : Carrier f g) : Option L :=
  match x.down with | .inl l => some l | .inr _ => none

noncomputable def rightProjection (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x : Carrier f g) : Option R := by
  classical
  exact match x.down with
    | .inl l => if h : l ∈ Set.range f.point then some (g.point (Classical.choose h)) else none
    | .inr r => some r.val

theorem left_injective (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) : Function.Injective (leftPoint f g) := by
  intro x y he
  exact Sum.inl_injective (congrArg ULift.down he)

theorem right_on_base (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x : A) :
    rightPoint f g (g.point x) = leftPoint f g (f.point x) := by
  classical
  have hx : g.point x ∈ Set.range g.point := ⟨x,rfl⟩
  unfold rightPoint leftPoint
  rw [dif_pos hx]
  have hh := g.injective (Classical.choose_spec hx)
  rw [hh]

@[simp] theorem leftProjection_left (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (l : L) :
    leftProjection f g (leftPoint f g l) = some l := rfl

@[simp] theorem rightProjection_right (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (r : R) :
    rightProjection f g (rightPoint f g r) = some r := by
  classical
  by_cases hr : r ∈ Set.range g.point
  · obtain ⟨x,rfl⟩ := hr
    rw [right_on_base]
    have hx : f.point x ∈ Set.range f.point := ⟨x,rfl⟩
    simp only [rightProjection,leftPoint,dif_pos hx]
    exact congrArg (fun z => some (g.point z)) (f.injective (Classical.choose_spec hx))
  · simp only [rightPoint,dif_neg hr,rightProjection]

theorem right_injective (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) : Function.Injective (rightPoint f g) := by
  intro x y he
  have hh := congrArg (rightProjection f g) he
  simpa only [rightProjection_right,Option.some.injEq] using hh

theorem intersection (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (l : L) (r : R) :
    leftPoint f g l = rightPoint f g r ↔ ∃ x, f.point x = l ∧ g.point x = r := by
  classical
  constructor
  · intro he
    have hh := congrArg (rightProjection f g) he
    rw [rightProjection_right] at hh
    by_cases hl : l ∈ Set.range f.point
    · simp only [rightProjection,leftPoint,dif_pos hl,Option.some.injEq] at hh
      exact ⟨Classical.choose hl,Classical.choose_spec hl,hh⟩
    · simp only [rightProjection,leftPoint,dif_neg hl] at hh
      cases hh
  · rintro ⟨x,rfl,rfl⟩
    exact (right_on_base f g x).symm

theorem covered (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x : Carrier f g) :
    (∃ l, leftPoint f g l = x) ∨ (∃ r, rightPoint f g r = x) := by
  classical
  rcases x with ⟨x⟩
  cases x with
  | inl l => exact Or.inl ⟨l,rfl⟩
  | inr r =>
    refine Or.inr ⟨r.val,?_⟩
    simp only [rightPoint,dif_neg r.property]

theorem leftProjection_some (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x : Carrier f g) (l : L) :
    leftProjection f g x = some l ↔ leftPoint f g l = x := by
  rcases x with ⟨x⟩
  cases x <;> simp [leftProjection,leftPoint,eq_comm]

theorem rightProjection_some (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x : Carrier f g) (r : R) :
    rightProjection f g x = some r ↔ rightPoint f g r = x := by
  classical
  constructor
  · intro he
    rcases (covered f g x) with ⟨l,rfl⟩ | ⟨s,rfl⟩
    · by_cases hl : l ∈ Set.range f.point
      · have hh : g.point (Classical.choose hl) = r := by
          simpa only [rightProjection,leftPoint,dif_pos hl,Option.some.injEq] using he
        rw [← hh,right_on_base,Classical.choose_spec hl]
      · simp only [rightProjection,leftPoint,dif_neg hl] at he
        cases he
    · have hh : s = r := by simpa only [rightProjection_right,Option.some.injEq] using he
      rw [hh]
  · intro he
    rw [← he,rightProjection_right]

def sort (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x : Carrier f g) : ι :=
  match x.down with | .inl l => sortL l | .inr r => sortR r.val

@[simp] theorem sort_left (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (l : L) :
    sort f g (leftPoint f g l) = sortL l := rfl

@[simp] theorem sort_right (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (r : R) :
    sort f g (rightPoint f g r) = sortR r := by
  classical
  by_cases hr : r ∈ Set.range g.point
  · obtain ⟨x,rfl⟩ := hr
    rw [right_on_base,sort_left]
    exact (f.sort_eq x).trans (g.sort_eq x).symm
  · simp only [rightPoint,dif_neg hr,sort]

end FreeAmalgamConstruction
end CCO.ProfileHelly
