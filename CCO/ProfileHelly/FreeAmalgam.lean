import CCO.ProfileHelly.Embeddings
import CCO.ProfileHelly.Fill
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

abbrev Carrier (_f : Network.Embedding B.toNetwork C.toNetwork)
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
  rw [dite_eq_left hx]
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
    simp only [rightProjection,leftPoint,dite_eq_left hx]
    exact congrArg (fun z => some (g.point z)) (f.injective (Classical.choose_spec hx))
  · simp only [rightPoint,dite_eq_right hr,rightProjection]

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
    · simp only [rightProjection,leftPoint,dite_eq_left hl,Option.some.injEq] at hh
      exact ⟨Classical.choose hl,Classical.choose_spec hl,hh⟩
    · simp only [rightProjection,leftPoint,dite_eq_right hl] at hh
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
    simp only [rightPoint,dite_eq_right r.property]

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
          simpa only [rightProjection,leftPoint,dite_eq_left hl,Option.some.injEq] using he
        rw [← hh,right_on_base,Classical.choose_spec hl]
      · simp only [rightProjection,leftPoint,dite_eq_right hl] at he
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
  · simp only [rightPoint,dite_eq_right hr,sort]

abbrev Tagged := Σ i, Σ j, Option (T.Atom i j)

def flipTagged (p : Tagged (T:=T)) : Tagged (T:=T) :=
  ⟨p.2.1,p.1,p.2.2.map T.conv⟩

theorem flip_networkTagged {X : Type*} {s : X → ι} (N : Network T s) (x y : X) :
    flipTagged (N.tagged x y) = N.tagged y x :=
  congrArg (fun e => (⟨s y,s x,e⟩ : Tagged (T:=T))) (N.edge_reverse y x)

theorem tagged_injective {i j : ι} {e e' : Option (T.Atom i j)}
    (h : (⟨i,j,e⟩ : Tagged (T:=T)) = ⟨i,j,e'⟩) : e = e' := by
  simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h

/-- Full inducedness over the WHOLE common base makes the literal tagged
edge independent of which factor is used on the intersection. -/
theorem overlap_tagged (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (l l' : L) (r r' : R)
    (h : leftPoint f g l = rightPoint f g r)
    (h' : leftPoint f g l' = rightPoint f g r') : C.tagged l l' = D.tagged r r' := by
  obtain ⟨x,rfl,rfl⟩ := (intersection f g l r).mp h
  obtain ⟨y,rfl,rfl⟩ := (intersection f g l' r').mp h'
  exact (f.preserves x y).trans (g.preserves x y).symm

noncomputable def taggedMatrix (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x y : Carrier f g) : Tagged (T:=T) :=
  match leftProjection f g x,leftProjection f g y with
  | some l,some l' => C.tagged l l'
  | _,_ => match rightProjection f g x,rightProjection f g y with
    | some r,some r' => D.tagged r r'
    | _,_ => ⟨sort f g x,sort f g y,none⟩

theorem taggedMatrix_left (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (l l' : L) :
    taggedMatrix f g (leftPoint f g l) (leftPoint f g l') = C.tagged l l' := by
  simp only [taggedMatrix,leftProjection_left]

theorem taggedMatrix_right (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (r r' : R) :
    taggedMatrix f g (rightPoint f g r) (rightPoint f g r') = D.tagged r r' := by
  cases hx : leftProjection f g (rightPoint f g r) <;>
    cases hy : leftProjection f g (rightPoint f g r')
  · simp only [taggedMatrix,hx,hy,rightProjection_right]
  · simp only [taggedMatrix,hx,hy,rightProjection_right]
  · simp only [taggedMatrix,hx,hy,rightProjection_right]
  · rename_i l l'
    simp only [taggedMatrix,hx,hy]
    exact overlap_tagged f g l l' r r'
      ((leftProjection_some f g _ l).mp hx) ((leftProjection_some f g _ l').mp hy)

theorem taggedMatrix_factor (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x y : Carrier f g) :
    (∃ l l', leftPoint f g l = x ∧ leftPoint f g l' = y ∧ taggedMatrix f g x y = C.tagged l l') ∨
    (∃ r r', rightPoint f g r = x ∧ rightPoint f g r' = y ∧ taggedMatrix f g x y = D.tagged r r') ∨
    taggedMatrix f g x y = ⟨sort f g x,sort f g y,none⟩ := by
  classical
  by_cases hL : ∃ l l', leftProjection f g x = some l ∧ leftProjection f g y = some l'
  · obtain ⟨l,l',hx,hy⟩ := hL
    exact Or.inl ⟨l,l',(leftProjection_some f g _ l).mp hx,
      (leftProjection_some f g _ l').mp hy,by simp only [taggedMatrix,hx,hy]⟩
  · have hm : taggedMatrix f g x y =
        match rightProjection f g x,rightProjection f g y with
        | some r,some r' => D.tagged r r'
        | _,_ => ⟨sort f g x,sort f g y,none⟩ := by
      cases hx : leftProjection f g x <;> cases hy : leftProjection f g y
      · simp only [taggedMatrix,hx,hy]
      · simp only [taggedMatrix,hx,hy]
      · simp only [taggedMatrix,hx,hy]
      · rename_i l l'
        exact False.elim (hL ⟨l,l',hx,hy⟩)
    by_cases hR : ∃ r r', rightProjection f g x = some r ∧ rightProjection f g y = some r'
    · obtain ⟨r,r',hx,hy⟩ := hR
      exact Or.inr (Or.inl ⟨r,r',(rightProjection_some f g _ r).mp hx,
        (rightProjection_some f g _ r').mp hy,by rw [hm,hx,hy]⟩)
    · right
      right
      rw [hm]
      cases hx : rightProjection f g x <;> cases hy : rightProjection f g y
      · rfl
      · rfl
      · rfl
      · rename_i r r'
        exact False.elim (hR ⟨r,r',hx,hy⟩)

theorem taggedMatrix_sorts (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x y : Carrier f g) :
    (taggedMatrix f g x y).1 = sort f g x ∧ (taggedMatrix f g x y).2.1 = sort f g y := by
  rcases taggedMatrix_factor f g x y with ⟨l,l',rfl,rfl,hm⟩ | ⟨r,r',rfl,rfl,hm⟩ | hm
  · rw [hm]
    exact ⟨rfl,rfl⟩
  · rw [hm]
    exact ⟨(sort_right f g r).symm,(sort_right f g r').symm⟩
  · rw [hm]
    exact ⟨rfl,rfl⟩

theorem taggedMatrix_diagonal (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x : Carrier f g) :
    taggedMatrix f g x x = ⟨sort f g x,sort f g x,none⟩ := by
  rcases covered f g x with ⟨l,rfl⟩ | ⟨r,rfl⟩
  · rw [taggedMatrix_left]
    simp only [Network.tagged,C.diagonal,sort_left]
  · rw [taggedMatrix_right]
    simp only [Network.tagged,D.diagonal]
    exact congrArg (fun i => (⟨i,i,none⟩ : Tagged (T:=T))) (sort_right f g r).symm

theorem taggedMatrix_reverse (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x y : Carrier f g) :
    flipTagged (taggedMatrix f g x y) = taggedMatrix f g y x := by
  have hR (X Y : Option R) :
      flipTagged (match X,Y with
        | some r,some r' => D.tagged r r'
        | _,_ => ⟨sort f g x,sort f g y,none⟩) =
      (match Y,X with
        | some r',some r => D.tagged r' r
        | _,_ => ⟨sort f g y,sort f g x,none⟩) := by
    cases X with
    | none => cases Y <;> rfl
    | some r =>
      cases Y with
      | none => rfl
      | some r' => exact flip_networkTagged D.toNetwork r r'
  cases hx : leftProjection f g x <;> cases hy : leftProjection f g y
  · simpa only [taggedMatrix,hx,hy] using hR (rightProjection f g x) (rightProjection f g y)
  · simpa only [taggedMatrix,hx,hy] using hR (rightProjection f g x) (rightProjection f g y)
  · simpa only [taggedMatrix,hx,hy] using hR (rightProjection f g x) (rightProjection f g y)
  · rename_i l l'
    simpa only [taggedMatrix,hx,hy] using flip_networkTagged C.toNetwork l l'

private theorem reconstruct_tagged (m : Tagged (T:=T)) (i j : ι)
    (hi : m.1 = i) (hj : m.2.1 = j) :
    (⟨i,j,m.2.2.map (Network.castAtom hi hj)⟩ : Tagged (T:=T)) = m := by
  rcases m with ⟨k,l,e⟩
  cases hi
  cases hj
  cases e <;> rfl

noncomputable def amalgamEdge (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x y : Carrier f g) :
    Option (T.Atom (sort f g x) (sort f g y)) :=
  (taggedMatrix f g x y).2.2.map
    (Network.castAtom (taggedMatrix_sorts f g x y).1 (taggedMatrix_sorts f g x y).2)

theorem amalgamEdge_tagged (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x y : Carrier f g) :
    (⟨sort f g x,sort f g y,amalgamEdge f g x y⟩ : Tagged (T:=T)) = taggedMatrix f g x y :=
  reconstruct_tagged _ _ _ (taggedMatrix_sorts f g x y).1 (taggedMatrix_sorts f g x y).2

noncomputable def network (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) : Network T (sort f g) where
  edge := amalgamEdge f g
  diagonal := by
    intro x
    have ht := (amalgamEdge_tagged f g x x).trans (taggedMatrix_diagonal f g x)
    exact tagged_injective ht
  edge_reverse := by
    intro x y
    have ht := taggedMatrix_reverse f g y x
    rw [← amalgamEdge_tagged f g y x,← amalgamEdge_tagged f g x y] at ht
    exact tagged_injective ht

theorem network_tagged (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x y : Carrier f g) :
    (network f g).tagged x y = taggedMatrix f g x y := amalgamEdge_tagged f g x y

noncomputable def leftEmbedding (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) : Network.Embedding C.toNetwork (network f g) where
  point := leftPoint f g
  injective := left_injective f g
  preserves := fun x y => (network_tagged f g _ _).trans (taggedMatrix_left f g x y)

noncomputable def rightEmbedding (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) : Network.Embedding D.toNetwork (network f g) where
  point := rightPoint f g
  injective := right_injective f g
  preserves := fun x y => (network_tagged f g _ _).trans (taggedMatrix_right f g x y)

theorem edge_factor (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) (x y : Carrier f g)
    (h : (network f g).graph.Adj x y) :
    (∃ s t, leftPoint f g s = x ∧ leftPoint f g t = y) ∨
      (∃ s t, rightPoint f g s = x ∧ rightPoint f g t = y) := by
  rcases taggedMatrix_factor f g x y with ⟨l,l',hl,hl',_⟩ | ⟨r,r',hr,hr',_⟩ | hm
  · exact Or.inl ⟨l,l',hl,hl'⟩
  · exact Or.inr ⟨r,r',hr,hr'⟩
  · obtain ⟨a,ha⟩ := h
    have ht := (network_tagged f g x y).trans hm
    have hn : (network f g).edge x y = none := tagged_injective ht
    rw [hn] at ha
    cases ha

end FreeAmalgamConstruction

/-- C25: the actual finite exact partial pushout, including empty bases.
No algebraic cycle/completion/SAP hypothesis is part of this construction. -/
noncomputable def freeAmalgam [Finite A] [Finite L] [Finite R]
    (B : CompleteNetwork T sortA) (C : CompleteNetwork T sortL) (D : CompleteNetwork T sortR)
    (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork) : FreeAmalgam B C D f g where
  Carrier := FreeAmalgamConstruction.Carrier f g
  finiteCarrier := by
    classical
    let : Fintype L := Fintype.ofFinite _
    let : Fintype R := Fintype.ofFinite _
    exact Finite.of_injective ULift.down ULift.down_injective
  sort := FreeAmalgamConstruction.sort f g
  network := FreeAmalgamConstruction.network f g
  left := FreeAmalgamConstruction.leftEmbedding f g
  right := FreeAmalgamConstruction.rightEmbedding f g
  commutes := fun x => (FreeAmalgamConstruction.right_on_base f g x).symm
  intersection := FreeAmalgamConstruction.intersection f g
  covered := FreeAmalgamConstruction.covered f g
  edge_factor := FreeAmalgamConstruction.edge_factor f g
end CCO.ProfileHelly
