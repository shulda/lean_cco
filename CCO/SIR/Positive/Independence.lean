import CCO.SIR.Positive.Network
import CCO.SIR.Positive.FiniteMap

universe u v w t
namespace CCO.SIR.Positive
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)]

def SelectedPair (h : Selectors.HereditarySelector S)
    (C : Finset (Sigma X)) (x y : Sigma X) : Prop :=
  ∃ hD : StrongExact.Exact S (baseMenu S C x y),
    S.colour x.2 y.2 = some (h.choose (baseMenu S C x y) hD)

/-- The literal displayed selected relation, on arbitrary finite real sets.
The normalization, rather than an assumption that bases belong to the sides,
is essential at arbitrary overlaps. -/
def Independent (h : Selectors.HereditarySelector S)
    (A C B : Finset (Sigma X)) : Prop :=
  (∀ x ∈ A, x ∈ B → x ∈ C) ∧
  ∀ x ∈ A, ∀ y ∈ B, x ∉ C → y ∉ C → SelectedPair S h C x y

theorem independent_normalization (h : Selectors.HereditarySelector S)
    (A B C : Finset (Sigma X)) :
    Independent S h (A ∪ C) C (B ∪ C) ↔ Independent S h A C B := by
  constructor
  · intro hi
    refine ⟨fun x hx hy => hi.1 x (Finset.mem_union_left C hx) (Finset.mem_union_left C hy),?_⟩
    intro x hx y hy hxc hyc
    exact hi.2 x (Finset.mem_union_left C hx) y (Finset.mem_union_left C hy) hxc hyc
  · intro hi
    constructor
    · intro x hx hy
      rcases Finset.mem_union.mp hx with hx | hc
      · rcases Finset.mem_union.mp hy with hy | hc
        · exact hi.1 x hx hy
        · exact hc
      · exact hc
    · intro x hx y hy hxc hyc
      exact hi.2 x ((Finset.mem_union.mp hx).resolve_right hxc)
        y ((Finset.mem_union.mp hy).resolve_right hyc) hxc hyc

theorem independent_restriction (h : Selectors.HereditarySelector S)
    {A B C A' B' : Finset (Sigma X)} (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hi : Independent S h A C B) : Independent S h A' C B' :=
  ⟨fun x hx hy => hi.1 x (hA hx) (hB hy),
    fun x hx y hy hxc hyc => hi.2 x (hA hx) y (hB hy) hxc hyc⟩

theorem selectedPair_symmetry (K : Selectors.ExactCalculus S)
    (h : Selectors.HereditarySelector S) {C : Finset (Sigma X)} {x y : Sigma X}
    (hi : SelectedPair S h C x y) : SelectedPair S h C y x := by
  obtain ⟨hD,hcol⟩ := hi
  have hOpp : StrongExact.Exact S (baseMenu S C y x) := by
    rw [←baseMenu_opposite]
    exact K.opposite hD
  refine ⟨hOpp,?_⟩
  have hchoice : h.choose (baseMenu S C y x) hOpp = h.choose (S.opposite (baseMenu S C x y)) (K.opposite hD) := by
    congr 1
    exact (baseMenu_opposite S C x y).symm
  rw [hchoice,h.opposite (baseMenu S C x y) hD (K.opposite hD)]
  exact (S.colour_swap x.2 y.2 _).mp hcol

theorem independent_symmetry (K : Selectors.ExactCalculus S)
    (h : Selectors.HereditarySelector S) (A B C : Finset (Sigma X)) :
    Independent S h A C B ↔ Independent S h B C A := by
  have one : ∀ A B C, Independent S h A C B → Independent S h B C A := by
    intro A B C hi
    exact ⟨fun x hx hy => hi.1 x hy hx,
      fun x hx y hy hxc hyc => selectedPair_symmetry S K h (hi.2 y hy x hx hyc hxc)⟩
  exact ⟨one A B C,one B A C⟩

section Action
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)
include H

/-- Full tagged-base transport retains each literal original menu. -/
theorem baseMenu_transport (g : G) (C : Finset (Sigma X))
    {i j : ι} (x : X i) (y : X j) :
    baseMenu S (transport g C) ⟨i,g • x⟩ ⟨j,g • y⟩ =
      baseMenu S C ⟨i,x⟩ ⟨j,y⟩ := by
  have hc : ∀ {k l : ι} (a : X k) (b : X l), S.colour (g • a) (g • b) = S.colour a b :=
    fun a b => S.colourInvariant_of_homogeneous H g a b
  ext a
  constructor
  · intro ha c hC
    have h := ha (g • c) ((smul_mem_transport g C c).mpr hC)
    rcases c with ⟨k,c⟩
    simpa only [edgeMenu,Sigma.smul_mk,hc] using h
  · intro ha c hC
    obtain ⟨d,hd,rfl⟩ := (mem_transport g C c).mp hC
    rcases d with ⟨k,d⟩
    simpa only [edgeMenu,Sigma.smul_mk,hc] using ha ⟨k,d⟩ hd

theorem selectedPair_transport (g : G) (C : Finset (Sigma X))
    (h : Selectors.HereditarySelector S) (x y : Sigma X) :
    SelectedPair S h (transport g C) (g • x) (g • y) ↔ SelectedPair S h C x y := by
  rcases x with ⟨i,x⟩
  rcases y with ⟨j,y⟩
  simp only [SelectedPair,Sigma.smul_mk,baseMenu_transport S H g C,
    S.colourInvariant_of_homogeneous H g x y]

theorem independent_transport (h : Selectors.HereditarySelector S)
    (g : G) (A B C : Finset (Sigma X)) :
    Independent S h (transport g A) (transport g C) (transport g B) ↔
      Independent S h A C B := by
  constructor
  · intro hi
    constructor
    · intro x hx hy
      exact (smul_mem_transport g C x).mp
        (hi.1 (g • x) ((smul_mem_transport g A x).mpr hx) ((smul_mem_transport g B x).mpr hy))
    · intro x hx y hy hxc hyc
      apply (selectedPair_transport S H g C h x y).mp
      exact hi.2 (g • x) ((smul_mem_transport g A x).mpr hx)
        (g • y) ((smul_mem_transport g B y).mpr hy)
        (fun he => hxc ((smul_mem_transport g C x).mp he))
        (fun he => hyc ((smul_mem_transport g C y).mp he))
  · intro hi
    constructor
    · intro x hx hy
      obtain ⟨a,ha,rfl⟩ := (mem_transport g A x).mp hx
      apply (smul_mem_transport g C a).mpr
      exact hi.1 a ha ((smul_mem_transport g B a).mp hy)
    · intro x hx y hy hxc hyc
      obtain ⟨a,ha,rfl⟩ := (mem_transport g A x).mp hx
      obtain ⟨b,hb,rfl⟩ := (mem_transport g B y).mp hy
      apply (selectedPair_transport S H g C h a b).mpr
      exact hi.2 a ha b hb
        (fun he => hxc ((smul_mem_transport g C a).mpr he))
        (fun he => hyc ((smul_mem_transport g C b).mpr he))
end Action
end CCO.SIR.Positive
