import CCO.UnaryFreshFrames.Examples.MatchingOrbits

/-! The root-equality presentation is conservative over the original one
matching relation. In particular EVERY original closed partial isomorphism
extends: the auxiliary relations do not buy homogeneity. -/
namespace CCO.UnaryFreshFrames.Examples.Matching
open Structure

def matchRel (x y : Point) : Prop := sort x = 1 ∧ sort y = 2 ∧ root x = root y

def basicRoot (x y : Point) : Prop :=
  (sort x = 0 ∧ sort y = 0 ∧ operation false x = operation false y) ∨
  (sort x = 0 ∧ sort y = 1 ∧ operation false x = y) ∨
  (sort x = 0 ∧ sort y = 2 ∧ operation true x = y) ∨
  (sort x = 1 ∧ sort y = 0 ∧ operation false y = x) ∨
  (sort x = 2 ∧ sort y = 0 ∧ operation true y = x) ∨
  (sort x = 1 ∧ sort y = 1 ∧ x = y) ∨
  (sort x = 2 ∧ sort y = 2 ∧ x = y) ∨ matchRel x y ∨ matchRel y x

theorem root_iff_basic (x y : Point) : root x = root y ↔ basicRoot x y := by
  rcases x with ⟨q,n⟩ | (q | q)
  all_goals rcases y with ⟨r,m⟩ | (r | r)
  all_goals simp [basicRoot,matchRel,sort,root,operation,rootPoint,partner]
  all_goals exact eq_comm

abbrev originalLanguage : Language where
  Sorts := Fin 3
  Func := Bool
  Rel := Unit
  input _ := 0
  output F := if F then 2 else 1
  arity _ := 2
  argument _ i := if i = 0 then 1 else 2

abbrev originalModel : Structure originalLanguage Point where
  sort := sort
  func := operation
  func_sort := model.func_sort
  func_offsort := model.func_offsort
  rel _ xs := matchRel (xs 0) (xs 1)
  rel_sort := by
    intro R xs h i
    fin_cases i
    · exact h.1
    · exact h.2.1

abbrev expandedPiece (A : originalModel.Piece) : model.Piece :=
  ⟨A.points,A.finite,A.closed⟩

theorem originalEmbedding_root_iff (A : originalModel.Piece)
    (f : A.Embedding Set.univ) (x y : A.points) :
    root (f.point x) = root (f.point y) ↔ root x.val = root y.val := by
  have hs (z : A.points) : sort (f.point z) = sort z.val := f.sort_eq z
  have he (a b : A.points) : f.point a = f.point b ↔ a.val = b.val :=
    f.injective.eq_iff.trans Subtype.ext_iff
  have ho (F : Bool) (a b : A.points) :
      operation F (f.point a) = f.point b ↔ operation F a.val = b.val := by
    have hfa : f.point (A.func F a) = operation F (f.point a) := f.func_eq F a
    rw [← hfa]
    exact he _ _
  have hoo (F : Bool) (a b : A.points) :
      operation F (f.point a) = operation F (f.point b) ↔
        operation F a.val = operation F b.val := by
    have hfa : f.point (A.func F a) = operation F (f.point a) := f.func_eq F a
    have hfb : f.point (A.func F b) = operation F (f.point b) := f.func_eq F b
    rw [← hfa, ← hfb]
    exact he _ _
  have hm (a b : A.points) : matchRel (f.point a) (f.point b) ↔ matchRel a.val b.val :=
    f.rel_iff () ![a,b]
  rw [root_iff_basic,root_iff_basic]
  simp only [basicRoot,hs,he,ho,hoo,hm]

def expandedEmbedding {A : originalModel.Piece} (f : A.Embedding Set.univ) :
    (expandedPiece A).Embedding Set.univ where
  point := f.point
  mem_point := f.mem_point
  injective := f.injective
  sort_eq := f.sort_eq
  func_eq := f.func_eq
  rel_iff := by
    intro R xs
    change (sort (f.point (xs 0)) = R.1 ∧ sort (f.point (xs 1)) = R.2 ∧
      root (f.point (xs 0)) = root (f.point (xs 1))) ↔
      (sort (xs 0).val = R.1 ∧ sort (xs 1).val = R.2 ∧ root (xs 0).val = root (xs 1).val)
    have h0 : sort (f.point (xs 0)) = sort (xs 0).val := f.sort_eq _
    have h1 : sort (f.point (xs 1)) = sort (xs 1).val := f.sort_eq _
    rw [h0,h1,originalEmbedding_root_iff]

def originalAut (g : model.Aut) : originalModel.Aut :=
  ⟨g.val,g.property.1,g.property.2.1,fun _ xs => g.property.2.2 (1,2) xs⟩

/-- Genuine homogeneity for the original language with ONLY the matching
relation, not merely for its conservative auxiliary presentation. -/
theorem original_homogeneous : originalModel.Homogeneous := by
  intro A f g
  obtain ⟨a,ha⟩ := homogeneous (expandedPiece A) (expandedEmbedding f) (expandedEmbedding g)
  exact ⟨originalAut a,ha⟩

theorem original_closure_eq (A : Set Point) : originalModel.closure A = model.closure A := by
  apply Set.Subset.antisymm
  · exact originalModel.closure_minimal (model.closure_closed A) (model.subset_closure A)
  · exact model.closure_minimal (originalModel.closure_closed A) (originalModel.subset_closure A)

theorem original_locallyFinite : originalModel.LocallyFinite := by
  intro A hA
  rw [original_closure_eq]
  exact locallyFinite A hA

theorem automorphisms_eq : originalModel.automorphisms = model.automorphisms := by
  ext e
  constructor
  · rintro ⟨hs,hf,hm⟩
    have hs' (x : Point) : sort (e x) = sort x := hs x
    have hf' (F : Bool) (x : Point) : e (operation F x) = operation F (e x) := hf F x
    have hm' (x y : Point) : matchRel (e x) (e y) ↔ matchRel x y := hm () ![x,y]
    have hroot (x y : Point) : root (e x) = root (e y) ↔ root x = root y := by
      rw [root_iff_basic,root_iff_basic]
      simp only [basicRoot,hs',← hf',e.injective.eq_iff,hm']
    refine ⟨hs,hf,?_⟩
    intro R xs
    change (sort (e (xs 0)) = R.1 ∧ sort (e (xs 1)) = R.2 ∧ root (e (xs 0)) = root (e (xs 1))) ↔
      (sort (xs 0) = R.1 ∧ sort (xs 1) = R.2 ∧ root (xs 0) = root (xs 1))
    rw [hs',hs',hroot]
  · rintro ⟨hs,hf,hr⟩
    exact ⟨hs,hf,fun _ xs => hr (1,2) xs⟩

theorem original_real_base_orbits (D : Set Point) (hD : D.Finite)
    (hReal : ∀ x ∈ D, sort x = 0) (u : Point) (hu : u ∉ originalModel.closure D) :
    (orbitOver originalModel.Aut D u).Infinite := by
  rw [original_closure_eq] at hu
  change (orbitOver originalModel.automorphisms D u).Infinite
  rw [automorphisms_eq]
  exact real_base_orbits D hD hReal u hu

end CCO.UnaryFreshFrames.Examples.Matching
