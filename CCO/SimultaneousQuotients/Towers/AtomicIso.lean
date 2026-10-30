import CCO.RawExact.QuotientSourcePalette

/-! An equivariant sortwise bijection induces a canonical bijection of
ALL actual diversity orbital names, preserving and reflecting their relations.
These names are actual full pair-orbital predicates, not arbitrary charts. -/

universe u v q t
namespace CCO.SimultaneousQuotients.Towers
open RawExact.QuotientPalette

variable {ι : Type u} {A : ι → Type v} {B : ι → Type q}
variable {G : Type t} [Group G] [∀ i, MulAction G (A i)] [∀ i, MulAction G (B i)]
variable (e : ∀ i, A i ≃ B i)
variable (he : ∀ i (g : G) x, e i (g • x) = g • e i x)

include he in
theorem equiv_orbital_iff {i j : ι} (a x : A i) (b y : A j) :
    GroupActions.orbital (G := G) a b x y ↔
      GroupActions.orbital (G := G) (e i a) (e j b) (e i x) (e j y) := by
  constructor
  · rintro ⟨g,rfl,rfl⟩
    exact ⟨g,(he i g a).symm,(he j g b).symm⟩
  · rintro ⟨g,hx,hy⟩
    exact ⟨g,(e i).injective ((he i g a).trans hx),
      (e j).injective ((he j g b).trans hy)⟩

/-- Transport an actual diversity orbital name, as its actual relation. -/
noncomputable def mapAtom {i j : ι} (a : DiversityAtom (G := G) A i j) :
    DiversityAtom (G := G) B i j := by
  refine ⟨fun x y => a.val ((e i).symm x) ((e j).symm y),?_,?_⟩
  · obtain ⟨x,y,hxy⟩ := a.property.1
    refine ⟨e i x,e j y,?_⟩
    funext p q
    apply propext
    rw [hxy]
    exact (equiv_orbital_iff e he x ((e i).symm p) y ((e j).symm q)).trans
      (by simp only [Equiv.apply_symm_apply])
  · intro x y hxy htag
    cases htag
    exact a.property.2 _ _ hxy rfl

@[simp] theorem mapAtom_relation {i j : ι}
    (a : DiversityAtom (G := G) A i j) (x : A i) (y : A j) :
    (mapAtom e he a).val (e i x) (e j y) ↔ a.val x y := by
  change a.val ((e i).symm (e i x)) ((e j).symm (e j y)) ↔ _
  simp only [Equiv.symm_apply_apply]

include he in
theorem symm_equivariant (i : ι) (g : G) (x : B i) :
    (e i).symm (g • x) = g • (e i).symm x := by
  apply (e i).injective
  rw [Equiv.apply_symm_apply,he,Equiv.apply_symm_apply]

/-- The atom map is bijective, including all cross-sort palettes. -/
noncomputable def atomEquiv (i j : ι) :
    DiversityAtom (G := G) A i j ≃ DiversityAtom (G := G) B i j where
  toFun := mapAtom e he
  invFun := mapAtom (fun k => (e k).symm) (symm_equivariant e he)
  left_inv a := by
    apply Subtype.ext
    funext x y
    change a.val ((e i).symm (e i x)) ((e j).symm (e j y)) = a.val x y
    simp only [Equiv.symm_apply_apply]
  right_inv a := by
    apply Subtype.ext
    funext x y
    change a.val (e i ((e i).symm x)) (e j ((e j).symm y)) = a.val x y
    simp only [Equiv.apply_symm_apply]

@[simp] theorem atomEquiv_relation {i j : ι}
    (a : DiversityAtom (G := G) A i j) (x : A i) (y : A j) :
    (atomEquiv e he i j a).val (e i x) (e j y) ↔ a.val x y :=
  mapAtom_relation e he a x y

end CCO.SimultaneousQuotients.Towers
