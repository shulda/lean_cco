import CCO.SIR.Positive.Basic
import CCO.Selectors.SourceCalculus
import CCO.Selectors.SourceSelectors

/-! Literal strong base-path menus of finite actual sets. The conditional
proofs consume an exact calculus, not its CCO derivation. -/
universe u v w t
namespace CCO.SIR.Positive
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)]

def edgeMenu (x y : Sigma X) : S.Menu x.1 y.1 :=
  {a | S.colour x.2 y.2 = some a}

def baseMenu (C : Finset (Sigma X)) (x y : Sigma X) : S.Menu x.1 y.1 :=
  {a | ∀ c ∈ C, a ∈ S.product (edgeMenu S x c) (edgeMenu S c y)}

@[simp] theorem edgeMenu_of_colour {x y : Sigma X} {a : S.Atom x.1 y.1}
    (h : S.colour x.2 y.2 = some a) : edgeMenu S x y = {a} := by
  ext b
  simp only [edgeMenu, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [h, Option.some.injEq]
  exact eq_comm

@[simp] theorem baseMenu_empty (x y : Sigma X) : baseMenu S ∅ x y = Set.univ := by
  ext a
  simp [baseMenu]

@[simp] theorem baseMenu_union (B C : Finset (Sigma X)) (x y : Sigma X) :
    baseMenu S (B ∪ C) x y = baseMenu S B x y ∩ baseMenu S C x y := by
  ext a
  simp [baseMenu, forall_and]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc),fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

/-- C08: split off exactly the genuinely new base vertices. -/
theorem baseMenu_enlarge (B C : Finset (Sigma X)) (x y : Sigma X) :
    baseMenu S (B ∪ C) x y = baseMenu S C x y ∩ baseMenu S (B \ C) x y := by
  ext a
  simp only [baseMenu, Set.mem_setOf_eq, Finset.mem_union, Set.mem_inter_iff,Finset.mem_sdiff]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inr hc),fun c hc => h c (Or.inl hc.1)⟩
  · rintro ⟨hC,hB⟩ c (hc|hc)
    · by_cases h : c ∈ C
      · exact hC c h
      · exact hB c ⟨hc,h⟩
    · exact hC c hc

/-- An actual cross atom survives every actual base-path constraint. -/
theorem actual_mem_baseMenu (C : Finset (Sigma X)) {x y : Sigma X}
    (hx : x ∉ C) (hy : y ∉ C) {a : S.Atom x.1 y.1}
    (ha : S.colour x.2 y.2 = some a) : a ∈ baseMenu S C x y := by
  intro c hc
  have hxc : x ≠ c := by rintro rfl; exact hx hc
  have hcy : c ≠ y := by rintro rfl; exact hy hc
  obtain ⟨p,hp⟩ := S.some_colour_of_ne x.2 c.2 hxc
  obtain ⟨q,hq⟩ := S.some_colour_of_ne c.2 y.2 hcy
  exact ⟨p,hp,q,hq,x.2,c.2,y.2,hp,hq,ha⟩

theorem baseMenu_nonempty (C : Finset (Sigma X)) {x y : Sigma X}
    (hx : x ∉ C) (hy : y ∉ C) (hxy : x ≠ y) :
    (baseMenu S C x y).Nonempty := by
  obtain ⟨a,ha⟩ := S.some_colour_of_ne x.2 y.2 hxy
  exact ⟨a,actual_mem_baseMenu S C hx hy ha⟩

noncomputable def baseMenus (C : Finset (Sigma X)) (x y : Sigma X) : List (S.Menu x.1 y.1) :=
  C.toList.map (fun c => S.product (edgeMenu S x c) (edgeMenu S c y))

theorem baseMenus_meet (C : Finset (Sigma X)) (x y : Sigma X) :
    StrongExact.meetMenus S (baseMenus S C x y) = baseMenu S C x y := by
  ext a
  constructor
  · intro ha c hc
    exact ha _ (List.mem_map.mpr ⟨c,Finset.mem_toList.mpr hc,rfl⟩)
  · intro ha D hD
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hD
    exact ha c (Finset.mem_toList.mp hc)

/-- C02: exactness is finite exact meet closure, with its evaluated
nonemptiness supplied by a genuine actual atom. -/
theorem baseMenu_exact (C : Selectors.ExactCalculus S)
    (B : Finset (Sigma X)) {x y : Sigma X}
    (hx : x ∉ B) (hy : y ∉ B) (hxy : x ≠ y) :
    StrongExact.Exact S (baseMenu S B x y) := by
  have hE : ∀ D ∈ baseMenus S B x y, StrongExact.Exact S D := by
    intro D hD
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hD
    have hc' : c ∈ B := Finset.mem_toList.mp hc
    have hxc : x ≠ c := by rintro rfl; exact hx hc'
    have hcy : c ≠ y := by rintro rfl; exact hy hc'
    obtain ⟨p,hp⟩ := S.some_colour_of_ne x.2 c.2 hxc
    obtain ⟨q,hq⟩ := S.some_colour_of_ne c.2 y.2 hcy
    rw [edgeMenu_of_colour S hp,edgeMenu_of_colour S hq]
    exact C.product (StrongExact.exact_singleton S p) (StrongExact.exact_singleton S q)
  have hn : (StrongExact.meetMenus S (baseMenus S B x y)).Nonempty := by
    rw [baseMenus_meet]
    exact baseMenu_nonempty S B hx hy hxy
  have he := StrongExact.exact_meetMenus_of_nonempty S _ hE hn
  rwa [baseMenus_meet] at he

/-- Converse of the actual optional-colour singleton menu, including
empty diagonal menus. -/
theorem edgeMenu_opposite (x y : Sigma X) :
    S.opposite (edgeMenu S x y) = edgeMenu S y x := by
  ext a
  change S.colour x.2 y.2 = some (S.conv a) ↔ S.colour y.2 x.2 = some a
  simpa only [S.conv_invol] using S.colour_swap x.2 y.2 (S.conv a)

theorem baseMenu_opposite (C : Finset (Sigma X)) (x y : Sigma X) :
    S.opposite (baseMenu S C x y) = baseMenu S C y x := by
  ext a
  constructor
  · intro ha c hc
    have hh : a ∈ S.opposite (S.product (edgeMenu S x c) (edgeMenu S c y)) := ha c hc
    rwa [S.product_opposite,edgeMenu_opposite,edgeMenu_opposite] at hh
  · intro ha c hc
    have hh : S.conv a ∈ S.opposite (S.product (edgeMenu S y c) (edgeMenu S c x)) :=
      S.mem_opposite (ha c hc)
    rwa [S.product_opposite,edgeMenu_opposite,edgeMenu_opposite] at hh

end CCO.SIR.Positive
