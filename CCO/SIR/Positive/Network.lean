import CCO.SIR.Positive.FreeSpan

universe u v w
namespace CCO.SIR.Positive
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)]

inductive SpanSide | left | base | right deriving DecidableEq

def spanSide (A C : Finset (Sigma X)) (x : Sigma X) : SpanSide :=
  if x ∈ C then .base else if x ∈ A then .left else .right

def crossSide : SpanSide → SpanSide → Bool
  | .left,.right | .right,.left => true
  | _,_ => false

theorem crossSide_symm (a b : SpanSide) : crossSide a b = crossSide b a := by
  cases a <;> cases b <;> rfl

@[simp] theorem spanSide_base (A C : Finset (Sigma X)) (x : Sigma X) :
    spanSide A C x = .base ↔ x ∈ C := by simp [spanSide]; split_ifs <;> simp_all

def freeMenu (A C : Finset (Sigma X)) (x y : Sigma X) : S.Menu x.1 y.1 :=
  if crossSide (spanSide A C x) (spanSide A C y) then baseMenu S C x y else edgeMenu S x y

private theorem cross_not_base {A C : Finset (Sigma X)} {x y : Sigma X}
    (h : crossSide (spanSide A C x) (spanSide A C y) = true) : x ∉ C ∧ y ∉ C := by
  constructor
  · intro hx
    have : spanSide A C x = .base := (spanSide_base A C x).mpr hx
    rw [this] at h
    cases hs : spanSide A C y <;> simp [crossSide,hs] at h
  · intro hy
    have : spanSide A C y = .base := (spanSide_base A C y).mpr hy
    rw [this] at h
    cases hs : spanSide A C x <;> simp [crossSide,hs] at h

theorem freeMenu_opposite (A C : Finset (Sigma X)) (x y : Sigma X) :
    S.opposite (freeMenu S A C x y) = freeMenu S A C y x := by
  unfold freeMenu
  rw [crossSide_symm (spanSide A C y) (spanSide A C x)]
  split_ifs
  · exact baseMenu_opposite S C x y
  · exact edgeMenu_opposite S x y

theorem actual_mem_freeMenu (A C : Finset (Sigma X)) {x y : Sigma X}
    {a : S.Atom x.1 y.1} (ha : S.colour x.2 y.2 = some a) :
    a ∈ freeMenu S A C x y := by
  unfold freeMenu
  split_ifs with h
  · obtain ⟨hx,hy⟩ := cross_not_base h
    exact actual_mem_baseMenu S C hx hy ha
  · exact ha

theorem freeMenu_exact (K : Selectors.ExactCalculus S)
    (A C : Finset (Sigma X)) {x y : Sigma X} (hxy : x ≠ y) :
    StrongExact.Exact S (freeMenu S A C x y) := by
  unfold freeMenu
  split_ifs with h
  · obtain ⟨hx,hy⟩ := cross_not_base h
    exact baseMenu_exact S K C hx hy hxy
  · obtain ⟨a,ha⟩ := S.some_colour_of_ne x.2 y.2 hxy
    rw [edgeMenu_of_colour S ha]
    exact StrongExact.exact_singleton S a

private theorem right_support (K : Selectors.ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (C : Finset (Sigma X)) {x y z : Sigma X}
    (hx : x ∉ C) (hy : y ∉ C) (hz : z ∉ C)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    baseMenu S C x z ⊆ S.product (baseMenu S C x y) (edgeMenu S y z) := by
  intro a ha
  have hop := S.mem_opposite ha
  rw [baseMenu_opposite] at hop
  have h := baseMenu_left_support S K hPoint hEdge C hz hy hx hyz.symm hxy.symm hxz.symm hop
  have hh := S.mem_opposite h
  rwa [S.product_opposite,edgeMenu_opposite,baseMenu_opposite,S.conv_invol] at hh

/-- Every ordered forward coordinate of the complete free-span network. -/
theorem freeMenu_support (K : Selectors.ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (A C : Finset (Sigma X)) {x y z : Sigma X}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    freeMenu S A C x z ⊆ S.product (freeMenu S A C x y) (freeMenu S A C y z) := by
  by_cases hcross : crossSide (spanSide A C x) (spanSide A C z) = true
  · obtain ⟨hx,hz⟩ := cross_not_base hcross
    have hxb : spanSide A C x ≠ .base := fun he => hx ((spanSide_base A C x).mp he)
    have hzb : spanSide A C z ≠ .base := fun he => hz ((spanSide_base A C z).mp he)
    by_cases hy : y ∈ C
    · have hyb := (spanSide_base A C y).mpr hy
      simp only [freeMenu,hcross,Bool.true_eq,ite_true,hyb]
      cases hsx : spanSide A C x <;> cases hsz : spanSide A C z <;>
        simp_all [crossSide]
      all_goals exact fun a ha => ha y hy
    · have hyb : spanSide A C y ≠ .base := fun he => hy ((spanSide_base A C y).mp he)
      cases hsx : spanSide A C x <;> cases hsy : spanSide A C y <;>
        cases hsz : spanSide A C z <;> simp_all only [crossSide,ne_eq,not_true_eq_false,
          Bool.false_eq_true,SpanSide.noConfusion,not_false_eq_true]
      all_goals simp only [freeMenu,hsx,hsy,hsz,crossSide,Bool.true_eq,Bool.false_eq_true,ite_true,ite_false]
      all_goals first
        | exact baseMenu_left_support S K hPoint hEdge C hx hy hz hxy hyz hxz
        | exact right_support S K hPoint hEdge C hx hy hz hxy hyz hxz
  · have hfalse : crossSide (spanSide A C x) (spanSide A C z) = false := by
      cases h : crossSide (spanSide A C x) (spanSide A C z) <;> simp_all
    simp only [freeMenu,hfalse,Bool.false_eq_true,ite_false]
    intro a ha
    obtain ⟨p,hp⟩ := S.some_colour_of_ne x.2 y.2 hxy
    obtain ⟨q,hq⟩ := S.some_colour_of_ne y.2 z.2 hyz
    exact ⟨p,actual_mem_freeMenu S A C hp,q,actual_mem_freeMenu S A C hq,
      x.2,y.2,z.2,hp,hq,ha⟩

/-- C03: all THREE coordinates, for every ordered distinct triple;
named sorts may repeat without restriction. -/
theorem freeMenu_PC (K : Selectors.ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (A C : Finset (Sigma X)) {x y z : Sigma X}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    S.PC (freeMenu S A C x y) (freeMenu S A C y z) (freeMenu S A C x z) := by
  refine ⟨freeMenu_support S K hPoint hEdge A C hxy hyz hxz,?_,?_⟩
  · have h := freeMenu_support S K hPoint hEdge A C hxz hyz.symm hxy
    rwa [←freeMenu_opposite S A C y z] at h
  · have h := freeMenu_support S K hPoint hEdge A C hxy.symm hxz hyz
    rwa [←freeMenu_opposite S A C x y] at h

end CCO.SIR.Positive
