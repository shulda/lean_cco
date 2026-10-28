import CCO.SIR.Positive.Menus

/-! All-coordinate path consistency of the free-span domains. -/
universe u v w
namespace CCO.SIR.Positive
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)]

private theorem meet_cons {i j : ι} (D : S.Menu i j) (Ds : List (S.Menu i j)) :
    StrongExact.meetMenus S (D::Ds) = D ∩ StrongExact.meetMenus S Ds := by
  ext a
  simp [StrongExact.meetMenus]

/-- Binary exact distribution plus strong Top absorption gives the
finite form, INCLUDING the empty restriction family. -/
theorem product_meetMenus (C : Selectors.ExactCalculus S)
    (hPoint : S.RealPointGluing) {i j k : ι} (P : S.Menu i j)
    (hP : StrongExact.Exact S P) (Ds : List (S.Menu j k))
    (hDs : ∀ D ∈ Ds, StrongExact.Exact S D)
    (hne : (StrongExact.meetMenus S Ds).Nonempty) :
    S.product P (StrongExact.meetMenus S Ds) =
      {a | ∀ D ∈ Ds, a ∈ S.product P D} := by
  induction Ds with
  | nil =>
    have hnil : StrongExact.meetMenus S ([] : List (S.Menu j k)) = Set.univ := by
      ext a; simp [StrongExact.meetMenus]
    rw [hnil,S.product_top_of_point_gluing hPoint P hP.1]
    ext a
    simp
  | cons D Ds ih =>
    have hD := hDs D (List.mem_cons_self)
    have hTail : ∀ E ∈ Ds, StrongExact.Exact S E := fun E hE => hDs E (List.mem_cons_of_mem D hE)
    have hnTail : (StrongExact.meetMenus S Ds).Nonempty := by
      obtain ⟨a,ha⟩ := hne
      exact ⟨a,fun E hE => ha E (List.mem_cons_of_mem D hE)⟩
    have hTailE := StrongExact.exact_meetMenus_of_nonempty S Ds hTail hnTail
    rw [meet_cons] at hne ⊢
    rw [C.distrib hP hD hTailE hne,ih hTail hnTail]
    ext a
    simp only [Set.mem_inter_iff,Set.mem_setOf_eq,List.mem_cons,forall_eq_or_imp]

/-- Move a fixed nonempty exact left multiplier through all base paths. -/
theorem product_baseMenu (C : Selectors.ExactCalculus S)
    (hPoint : S.RealPointGluing) (B : Finset (Sigma X))
    (x y : Sigma X) (hx : x ∉ B) (hy : y ∉ B) (hxy : x ≠ y)
    {i : ι} (P : S.Menu i x.1) (hP : StrongExact.Exact S P) :
    S.product P (baseMenu S B x y) =
      {a | ∀ c ∈ B, a ∈ S.product P (S.product (edgeMenu S x c) (edgeMenu S c y))} := by
  have hEach : ∀ D ∈ baseMenus S B x y, StrongExact.Exact S D := by
    intro D hD
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hD
    have hc' : c ∈ B := Finset.mem_toList.mp hc
    obtain ⟨p,hp⟩ := S.some_colour_of_ne x.2 c.2 (by intro he; exact hx ((show x = c from he).symm ▸ hc'))
    obtain ⟨q,hq⟩ := S.some_colour_of_ne c.2 y.2 (by intro he; exact hy ((show c = y from he) ▸ hc'))
    rw [edgeMenu_of_colour S hp,edgeMenu_of_colour S hq]
    exact C.product (StrongExact.exact_singleton S p) (StrongExact.exact_singleton S q)
  have hn : (StrongExact.meetMenus S (baseMenus S B x y)).Nonempty := by
    rw [baseMenus_meet]
    exact baseMenu_nonempty S B hx hy hxy
  rw [←baseMenus_meet S B x y,product_meetMenus S C hPoint P hP _ hEach hn]
  ext a
  simp only [Set.mem_setOf_eq,baseMenus,List.forall_mem_map,Finset.mem_toList]

/-- The nonliteral coordinate of a two-left/one-right free-span triangle.
Every intermediate colour is literal; finite exact distribution supplies
one common strong support across all base vertices. -/
theorem baseMenu_left_support (C : Selectors.ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (B : Finset (Sigma X)) {x y z : Sigma X}
    (hx : x ∉ B) (hy : y ∉ B) (hz : z ∉ B)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    baseMenu S B x z ⊆ S.product (edgeMenu S x y) (baseMenu S B y z) := by
  obtain ⟨p,hp⟩ := S.some_colour_of_ne x.2 y.2 hxy
  have hP : StrongExact.Exact S (edgeMenu S x y) := by
    rw [edgeMenu_of_colour S hp]
    exact StrongExact.exact_singleton S p
  rw [product_baseMenu S C hPoint B y z hy hz hyz _ hP]
  intro a ha c hc
  have hxc : x ≠ c := by rintro rfl; exact hx hc
  have hyc : y ≠ c := by rintro rfl; exact hy hc
  obtain ⟨q,hq⟩ := S.some_colour_of_ne x.2 c.2 hxc
  obtain ⟨r,hr⟩ := S.some_colour_of_ne y.2 c.2 hyc
  have hSub : edgeMenu S x c ⊆ S.product (edgeMenu S x y) (edgeMenu S y c) := by
    intro b hb
    have hbq : b = q := by simpa [edgeMenu,hq] using hb.symm
    subst b
    exact ⟨p,hp,r,hr,x.2,y.2,c.2,hp,hr,hq⟩
  have h := S.product_mono hSub (Set.Subset.refl (edgeMenu S c z)) (ha c hc)
  rwa [S.product_assoc_of_edge_gluing hEdge] at h

/-- All three literal coordinates of a genuine three-point triangle. -/
theorem edgeMenu_PC {x y z : Sigma X}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    S.PC (edgeMenu S x y) (edgeMenu S y z) (edgeMenu S x z) := by
  obtain ⟨p,hp⟩ := S.some_colour_of_ne x.2 y.2 hxy
  obtain ⟨q,hq⟩ := S.some_colour_of_ne y.2 z.2 hyz
  obtain ⟨r,hr⟩ := S.some_colour_of_ne x.2 z.2 hxz
  refine ⟨?_,?_,?_⟩
  · intro a ha
    have he : a = r := by simpa [edgeMenu,hr] using ha.symm
    subst a
    exact ⟨p,hp,q,hq,x.2,y.2,z.2,hp,hq,hr⟩
  · intro a ha
    have he : a = p := by simpa [edgeMenu,hp] using ha.symm
    subst a
    exact ⟨r,hr,S.conv q,S.mem_opposite hq,
      x.2,z.2,y.2,hr,(S.colour_swap y.2 z.2 q).mp hq,hp⟩
  · intro a ha
    have he : a = q := by simpa [edgeMenu,hq] using ha.symm
    subst a
    exact ⟨S.conv p,S.mem_opposite hp,r,hr,
      y.2,x.2,z.2,(S.colour_swap x.2 y.2 p).mp hp,hr,hq⟩

/-- C03 two-left/one-right: the old coordinate is supported by the
actual strong amalgam, the two free coordinates by finite distribution. -/
theorem baseMenu_PC (C : Selectors.ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (B : Finset (Sigma X)) {x y z : Sigma X}
    (hx : x ∉ B) (hy : y ∉ B) (hz : z ∉ B)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    S.PC (edgeMenu S x y) (baseMenu S B y z) (baseMenu S B x z) := by
  refine ⟨baseMenu_left_support S C hPoint hEdge B hx hy hz hxy hyz hxz,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq⟩ := S.some_colour_of_ne y.2 z.2 hyz
    obtain ⟨r,hr⟩ := S.some_colour_of_ne x.2 z.2 hxz
    exact ⟨r,actual_mem_baseMenu S B hx hz hr,S.conv q,
      S.mem_opposite (actual_mem_baseMenu S B hy hz hq),
      x.2,z.2,y.2,hr,(S.colour_swap y.2 z.2 q).mp hq,hp⟩
  · have h := baseMenu_left_support S C hPoint hEdge B hy hx hz hxy.symm hxz hyz
    rwa [←edgeMenu_opposite S x y] at h

/-- C03 through-base: literal definition gives the free coordinate;
the actual cross atom supplies both singleton coordinates. -/
theorem baseMenu_through_PC (B : Finset (Sigma X)) {x y z : Sigma X}
    (hx : x ∉ B) (hz : z ∉ B) (hy : y ∈ B) (hxz : x ≠ z) :
    S.PC (edgeMenu S x y) (edgeMenu S y z) (baseMenu S B x z) := by
  have hxy : x ≠ y := by rintro rfl; exact hx hy
  have hyz : y ≠ z := by rintro rfl; exact hz hy
  obtain ⟨p,hp⟩ := S.some_colour_of_ne x.2 y.2 hxy
  obtain ⟨q,hq⟩ := S.some_colour_of_ne y.2 z.2 hyz
  obtain ⟨r,hr⟩ := S.some_colour_of_ne x.2 z.2 hxz
  refine ⟨fun a ha => ha y hy,?_,?_⟩
  · intro a ha
    have he : a = p := by simpa [edgeMenu,hp] using ha.symm
    subst a
    exact ⟨r,actual_mem_baseMenu S B hx hz hr,S.conv q,S.mem_opposite hq,
      x.2,z.2,y.2,hr,(S.colour_swap y.2 z.2 q).mp hq,hp⟩
  · intro a ha
    have he : a = q := by simpa [edgeMenu,hq] using ha.symm
    subst a
    exact ⟨S.conv p,S.mem_opposite hp,r,actual_mem_baseMenu S B hx hz hr,
      y.2,x.2,z.2,(S.colour_swap x.2 y.2 p).mp hp,hr,hq⟩

end CCO.SIR.Positive
