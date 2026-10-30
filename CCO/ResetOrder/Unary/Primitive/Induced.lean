import CCO.ResetOrder.Unary.Primitive.Closure

universe u v
namespace CCO.ResetOrder.Unary.Primitive.Structure
variable {L : Signature.{u}} {V : Type v} (C : Structure L V)

def induce (S : Set V) (_hS : C.IsClosed S) : Structure L S where
  sort x := C.sort x.val
  func F x := {y | y.val ∈ C.func F x.val}
  functional F x y z hy hz := Subtype.ext (C.functional F x.val y.val z.val hy hz)
  func_sorted F x y hy := C.func_sorted F x.val y.val hy
  rel R xs := C.rel R (Subtype.val ∘ xs)
  rel_sorted R xs hx := C.rel_sorted R (Subtype.val ∘ xs) hx

def inclusion (S : Set V) (hS : C.IsClosed S) : Embedding (C.induce S hS) C where
  point := Subtype.val
  sort_eq _ := rfl
  map_func _ _ _ h := h
  map_rel _ _ h := h
  injective := Subtype.val_injective
  reflect_func F x y hy := ⟨⟨y, hS F x.val x.property hy⟩, hy, rfl⟩
  reflect_rel _ _ h := h

theorem isClosed_of_domain_reflecting {S : Set V} (D : Structure L S)
    (e : Embedding D C) (he : ∀ x, e.point x = x.val) : C.IsClosed S := by
  intro F x hx y hy
  obtain ⟨z, _, hz⟩ := e.reflect_func F ⟨x, hx⟩ y (by simpa only [he] using hy)
  rw [← hz, he]
  exact z.property

theorem induce_total {S : Set V} (hS : C.IsClosed S) (hC : C.Total) :
    (C.induce S hS).Total := by
  intro F x hx
  obtain ⟨y, hy⟩ := hC F x.val hx
  exact ⟨⟨y, hS F x.val x.property hy⟩, hy⟩

theorem isClosed_image {S : Set V} (hS : C.IsClosed S) {A : Set S}
    (hA : (C.induce S hS).IsClosed A) : C.IsClosed (Subtype.val '' A) := by
  rintro F x ⟨z, hz, rfl⟩ y hy
  let t : S := ⟨y, hS F z.val z.property hy⟩
  exact ⟨t, hA F z hz hy, rfl⟩

theorem closure_induce_image {S : Set V} (hS : C.IsClosed S) (B : Set S) :
    Subtype.val '' (C.induce S hS).closure B = C.closure (Subtype.val '' B) := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    apply (C.induce S hS).closure_minimal
      (S := {t | t.val ∈ C.closure (Subtype.val '' B)}) ?_ ?_ hz
    · intro F x hx y hy
      exact C.isClosed_closure _ F x.val hx hy
    · intro x hx
      exact C.subset_closure _ ⟨x, hx, rfl⟩
  · apply C.closure_minimal (C.isClosed_image hS ((C.induce S hS).isClosed_closure B))
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, (C.induce S hS).subset_closure B hx, rfl⟩

def closureStructure (B : Set V) : Structure L (C.closure B) :=
  C.induce (C.closure B) (C.isClosed_closure B)

def singletonStructure (x : V) : Structure L (C.closureAt x) := C.closureStructure {x}

theorem singleton_generated (x : V) :
    (C.singletonStructure x).closure {⟨x, C.mem_closureAt x⟩} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  have liftPath : ∀ {y}, Relation.ReflTransGen C.Step x y →
      ∃ t : C.closureAt x, t.val = y ∧
        Relation.ReflTransGen (C.singletonStructure x).Step ⟨x, C.mem_closureAt x⟩ t := by
    intro y h
    induction h with
    | refl => exact ⟨⟨x, C.mem_closureAt x⟩, rfl, .refl⟩
    | @tail y z h hs ih =>
      obtain ⟨t, ht, hp⟩ := ih
      obtain ⟨F, hF⟩ := hs
      have hz : z ∈ C.closureAt x := C.isClosed_closure {x} F y (ht ▸ t.property) hF
      refine ⟨⟨z, hz⟩, rfl, hp.tail ⟨F, ?_⟩⟩
      change z ∈ C.func F t.val
      simpa only [ht] using hF
  obtain ⟨y, hy, hp⟩ := z.property
  have hyx : y = x := hy
  obtain ⟨t, ht, hp'⟩ := liftPath (hyx ▸ hp)
  have htz : t = z := Subtype.ext ht
  exact ⟨⟨x, C.mem_closureAt x⟩, rfl, htz ▸ hp'⟩

end CCO.ResetOrder.Unary.Primitive.Structure
