import CCO.FullCode.Extension

/-! The actual inverse embedding maps, coordinate uniqueness and support maps. -/
universe u v w z a b
namespace CCO.FullCode
variable {L : Language.{u}} {V : Type v} {W : Type w} {Z : Type z}

theorem Root.ext_coordinates {C : Structure L V} {S : RootScheme L} {r s : Root C S}
    (ht : r.tag = s.tag) (hc : ∀ j, r.coordinate j = s.coordinate (ht ▸ j)) : r = s := by
  cases r with | mk rt rc rs rv =>
   cases s with | mk st sc ss sv =>
    change rt = st at ht
    cases ht
    have hcs : rc = sc := funext hc
    cases hcs
    rfl

theorem NormalForms.valid_of_embedding (N : NormalForms L)
    {C : Structure L V} {D : Structure L W} (f : Structure.Embedding C D)
    (hD : N.Valid D) : N.Valid C := by
  intro s t q x hx
  ext y
  rw [← q.map_iff f x y, ← (N.form s t (N.normalize q)).map_iff f x y]
  rw [hD s t q (f.point x) ((f.sort_eq x).trans hx)]

namespace Object
variable {C : Structure L V} {D : Structure L W} {E : Structure L Z}
  {S : RootScheme L} {A : Type a} {B : Type b} {N : NormalForms L}
  {O : Object C S A} {P : Object D S B}

theorem Embedding.extendPoint_coordinate (f : Embedding N O P) (hC : N.Valid C)
    (hD : N.Valid D) (a : A) (j : Fin (S.arity (O.root a).tag)) :
    f.extendPoint hC ⟨(O.root a).coordinate j, O.coordinate_mem_support a j⟩ =
      (P.root (f.point a)).coordinate ((f.tag_eq a).symm ▸ j) := by
  let q : Coordinate S := ⟨(O.root a).tag, j⟩
  have hx : (O.root a).coordinate j ∈ (O.root a).presentation N (Presentation.identity N q) := by
    rw [(O.root a).identity_presentation N hC q, Root.coordinateGraph_self]
    rfl
  have hy := f.extendPoint_presentation hC
    ⟨(O.root a).coordinate j, O.coordinate_mem_support a j⟩ a (Presentation.identity N q) hx
  rw [(P.root (f.point a)).identity_presentation N hD q] at hy
  obtain ⟨ht, he⟩ := hy
  exact he.symm

theorem embedding_unique_on_coordinates (O : Object C S A)
    {f g : Structure.Embedding O.supportStructure D}
    (h : ∀ a j, f.point ⟨(O.root a).coordinate j, O.coordinate_mem_support a j⟩ =
      g.point ⟨(O.root a).coordinate j, O.coordinate_mem_support a j⟩) : f = g := by
  apply Structure.Embedding.ext
  intro x
  obtain ⟨a, j, q, hpath⟩ :
      ∃ a j, ∃ q : Relation.ReflTransGen C.Step ((O.root a).coordinate j) x.val, True := by
    obtain ⟨y, ⟨a, j, rfl⟩, hp⟩ := x.property
    exact ⟨a, j, hp, trivial⟩
  have huniq : ∀ {y}, (hp : Relation.ReflTransGen C.Step ((O.root a).coordinate j) y) →
      ∀ hy : y ∈ O.support, f.point ⟨y, hy⟩ = g.point ⟨y, hy⟩ := by
    intro y hp
    induction hp with
    | refl => intro hy; exact h a j
    | @tail y z hp hs ih =>
      intro hz
      obtain ⟨F, hF⟩ := hs
      have hy : y ∈ O.support := by
        exact ⟨(O.root a).coordinate j, ⟨a, j, rfl⟩, hp⟩
      have hf := f.map_func F ⟨y, hy⟩ ⟨z, hz⟩ hF
      have hg := g.map_func F ⟨y, hy⟩ ⟨z, hz⟩ hF
      exact D.functional F (f.point ⟨y, hy⟩) _ _ hf ((ih hy).symm ▸ hg)
  exact huniq q x.property

noncomputable def Embedding.onSupport (f : Embedding N O P) (hC : N.Valid C) (hD : N.Valid D) :
    Structure.Embedding O.supportStructure P.supportStructure where
  point x := ⟨(f.extend hC hD).point x, by
    obtain ⟨a, p, _, hy⟩ := f.extendPoint_spec hC x
    exact P.presentation_mem_support N (f.point a) p hy⟩
  injective := by intro x y h; exact (f.extend hC hD).injective (congrArg Subtype.val h)
  sort_eq x := (f.extend hC hD).sort_eq x
  map_func F x y hy := (f.extend hC hD).map_func F x y hy
  reflect_func F x y hy := by
    obtain ⟨z, hz, he⟩ := (f.extend hC hD).reflect_func F x y.val hy
    exact ⟨z, hz, Subtype.ext he⟩
  unary_iff U x := (f.extend hC hD).unary_iff U x
  binary_iff R x y := (f.extend hC hD).binary_iff R x y

theorem fromHidden_extend (N : NormalForms L) (O : Object C S A) (hC : N.Valid C)
    (hD : N.Valid D) (f : Embedding N O (full D S)) :
    fromHidden N O (f.extend hC hD) = f := by
  apply Embedding.ext
  intro a
  apply Root.ext_coordinates (f.tag_eq a).symm
  intro j
  exact f.extendPoint_coordinate hC hD a j

theorem extend_fromHidden (N : NormalForms L) (O : Object C S A) (hC : N.Valid C)
    (hD : N.Valid D) (g : Structure.Embedding O.supportStructure D) :
    (fromHidden N O g).extend hC hD = g := by
  apply O.embedding_unique_on_coordinates
  intro a j
  exact (fromHidden N O g).extendPoint_coordinate hC hD a j

noncomputable def fullCodeEquiv (N : NormalForms L) (O : Object C S A)
    (hC : N.Valid C) (hD : N.Valid D) :
    Embedding N O (full D S) ≃ Structure.Embedding O.supportStructure D where
  toFun f := f.extend hC hD
  invFun := fromHidden N O
  left_inv := fromHidden_extend N O hC hD
  right_inv := extend_fromHidden N O hC hD

end Object
end CCO.FullCode
