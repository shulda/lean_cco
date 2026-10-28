import CCO.SIR.Positive.Independence

universe u v w t
namespace CCO.SIR.Positive
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)]
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- With the base fixed pointwise, moving just the left endpoint
retains every literal incident atom, and hence its entire original menu. -/
theorem baseMenu_fixed_left (H : HomogeneousSource S G) (g : G)
    (C : Finset (Sigma X)) (hfix : ∀ c ∈ C, g • c = c)
    {i j : ι} (x : X i) (y : X j) :
    baseMenu S C ⟨i,g • x⟩ ⟨j,y⟩ = baseMenu S C ⟨i,x⟩ ⟨j,y⟩ := by
  have hEdge : ∀ c ∈ C, edgeMenu S ⟨i,g • x⟩ c = edgeMenu S ⟨i,x⟩ c := by
    intro c hc
    have hgc := hfix c hc
    rcases c with ⟨k,c⟩
    have hgc' : g • c = c := by
      simpa only [Sigma.smul_mk,Sigma.mk.injEq,heq_eq_eq,true_and] using hgc
    have hcL := S.colourInvariant_of_homogeneous H g x c
    rw [hgc'] at hcL
    simp only [edgeMenu,hcL]
  ext a
  constructor
  · intro ha c hc
    have hh := ha c hc
    rwa [hEdge c hc] at hh
  · intro ha c hc
    rw [hEdge c hc]
    exact ha c hc

private theorem smul_not_mem_of_fix (g : G) (C : Finset (Sigma X))
    (hfix : ∀ c ∈ C, g • c = c) {x : Sigma X} (hx : x ∉ C) : g • x ∉ C := by
  intro h
  have he : g • x = x := MulAction.injective g (hfix (g • x) h)
  exact hx (he ▸ h)

/-- C12: each prescribed original finite map extends while the entire
other side and all named parameters stay fixed POINTWISE. -/
theorem independent_stationarity (H : HomogeneousSource S G)
    (h : Selectors.HereditarySelector S) (A B C : Finset (Sigma X)) (g : G)
    (hfix : ∀ c ∈ C, g • c = c)
    (hI : Independent S h A C B) (hI' : Independent S h (transport g A) C B) :
    ∃ k : G, (∀ b ∈ B ∪ C, k • b = b) ∧ ∀ a ∈ A, k • a = g • a := by
  apply extends_union_fixing H A B C g hfix hI.1
  intro a ha b hb
  by_cases haC : a ∈ C
  · rw [hfix a haC]
  by_cases hbC : b ∈ C
  · have hp := H.preserves_colours g a b
    rwa [hfix b hbC] at hp
  have hgaC := smul_not_mem_of_fix g C hfix haC
  obtain ⟨hD,hcol⟩ := hI.2 a ha b hb haC hbC
  obtain ⟨hD',hcol'⟩ := hI'.2 (g • a) ((smul_mem_transport g A a).mpr ha) b hb hgaC hbC
  rcases a with ⟨i,a⟩
  rcases b with ⟨j,b⟩
  change S.colour (g • a) b = some (h.choose (baseMenu S C ⟨i,g • a⟩ ⟨j,b⟩) hD') at hcol'
  have he := baseMenu_fixed_left S H g C hfix a b
  have hch : h.choose (baseMenu S C ⟨i,g • a⟩ ⟨j,b⟩) hD' =
      h.choose (baseMenu S C ⟨i,a⟩ ⟨j,b⟩) hD := by congr 1
  change (⟨i,j,S.colour (g • a) b⟩ : Σ i : ι, Σ j : ι, Option (S.Atom i j)) =
    ⟨i,j,S.colour a b⟩
  rw [hcol',hch,hcol]

end CCO.SIR.Positive
