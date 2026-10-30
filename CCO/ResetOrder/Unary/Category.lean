import CCO.UnarySupport.Induced

/-! Concrete induced embeddings retain every partial-unary domain and nullary relation. -/
universe u v w z
namespace CCO.ResetOrder.Unary
open CCO.UnarySupport

abbrev Hom {L : Signature.{u}} {V : Type v} {W : Type w}
    (A : Structure L V) (B : Structure L W) := Structure.Embedding A B

@[ext] theorem hom_ext {L : Signature.{u}} {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W} {f g : Hom A B}
    (h : ∀ x, f.point x = g.point x) : f = g := by
  cases f with
  | mk f fi ff fr =>
    cases g with
    | mk g gi gf gr =>
      have he : f = g := by
        cases f
        cases g
        congr
        exact funext h
      cases he
      rfl

def identity {L : Signature.{u}} {V : Type v} (A : Structure L V) : Hom A A where
  point x := x
  sort_eq _ := rfl
  map_func _ _ _ h := h
  map_rel _ _ h := h
  injective := Function.injective_id
  reflect_func _ _ y h := ⟨y,h,rfl⟩
  reflect_rel _ _ h := h

def compose {L : Signature.{u}} {V : Type v} {W : Type w} {Z : Type z}
    {A : Structure L V} {B : Structure L W} {C : Structure L Z}
    (g : Hom B C) (f : Hom A B) : Hom A C where
  point := g.point ∘ f.point
  sort_eq x := (g.sort_eq _).trans (f.sort_eq x)
  map_func F x y h := g.map_func F _ _ (f.map_func F x y h)
  map_rel R xs h := g.map_rel R _ (f.map_rel R xs h)
  injective := g.injective.comp f.injective
  reflect_func F x y h := by
    obtain ⟨b,hb,hby⟩ := g.reflect_func F _ y h
    obtain ⟨a,ha,hab⟩ := f.reflect_func F x b hb
    exact ⟨a,ha,(congrArg g.point hab).trans hby⟩
  reflect_rel R xs h := f.reflect_rel R xs (g.reflect_rel R _ h)

@[simp] theorem compose_point {L : Signature.{u}} {V : Type v} {W : Type w} {Z : Type z}
    {A : Structure L V} {B : Structure L W} {C : Structure L Z}
    (g : Hom B C) (f : Hom A B) (x : V) :
    (compose g f).point x = g.point (f.point x) := rfl

theorem range_closed {L : Signature.{u}} {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W} (f : Hom A B) :
    B.IsClosed (Set.range f.point) := by
  rintro F _ ⟨x,rfl⟩ y hy
  obtain ⟨z,_,rfl⟩ := f.reflect_func F x y hy
  exact ⟨z,rfl⟩

theorem map_closure {L : Signature.{u}} {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W} (f : Hom A B) (S : Set V) :
    f.point '' A.closure S = B.closure (f.point '' S) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y,⟨x,hx,hxy⟩,rfl⟩
    refine ⟨f.point x,⟨x,hx,rfl⟩,?_⟩
    induction hxy with
    | refl => exact .refl
    | tail h hs ih =>
      obtain ⟨F,hF⟩ := hs
      exact ih.tail ⟨F,f.map_func F _ _ hF⟩
  · apply B.closure_minimal
    · rintro F _ ⟨x,hx,rfl⟩ y hy
      obtain ⟨z,hz,rfl⟩ := f.reflect_func F x y hy
      exact ⟨z,A.isClosed_closure S F x hx hz,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨x,A.subset_closure S hx,rfl⟩

structure Iso {L : Signature.{u}} {V : Type v} {W : Type w}
    (A : Structure L V) (B : Structure L W) where
  hom : Hom A B
  surjective : Function.Surjective hom.point

noncomputable def Iso.inverse {L : Signature.{u}} {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W} (e : Iso A B) : Hom B A := by
  let inv := Function.surjInv e.surjective
  have hv : ∀y, e.hom.point (inv y) = y := Function.rightInverse_surjInv e.surjective
  refine {
    point := inv
    injective := Function.RightInverse.injective hv
    sort_eq := fun y => (e.hom.sort_eq (inv y)).symm.trans (congrArg B.sort (hv y))
    map_func := ?_
    reflect_func := ?_
    map_rel := ?_
    reflect_rel := ?_ }
  · intro F x y hy
    obtain ⟨a,ha,hea⟩ := e.hom.reflect_func F (inv x) y (by simpa only [hv] using hy)
    have hai : a = inv y := e.hom.injective (hea.trans (hv y).symm)
    exact hai ▸ ha
  · intro R xs h
    apply e.hom.reflect_rel R (inv ∘ xs)
    simpa only [Function.comp_assoc,Function.comp_def,hv] using h
  · intro F x y hy
    refine ⟨e.hom.point y,?_,?_⟩
    · simpa only [hv] using e.hom.map_func F (inv x) y hy
    · exact e.hom.injective (hv (e.hom.point y))
  · intro R xs h
    have h' := e.hom.map_rel R (inv ∘ xs) h
    simpa only [Function.comp_assoc,Function.comp_def,hv] using h'

end CCO.ResetOrder.Unary
