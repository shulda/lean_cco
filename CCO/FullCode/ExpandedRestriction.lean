import CCO.FullCode.Cofinality

/-! Actual expanded restriction and WHOLE-image old-root normalization. -/

universe u v w z
namespace CCO.FullCode.Structure
variable {L L₀ L₁ : Language.{u}} {V : Type v} {W : Type w} {Z : Type z}

def Embedding.targetCongr {A : Structure L V} {C D : Structure L W}
    (f : Embedding A C) (h : C = D) : Embedding A D where
  point := f.point
  injective := f.injective
  sort_eq x := by rw [← h]; exact f.sort_eq x
  map_func F x y hy := by rw [← h]; exact f.map_func F x y hy
  reflect_func F x y hy := by
    rw [← h] at hy
    exact f.reflect_func F x y hy
  unary_iff U x := by rw [← h]; exact f.unary_iff U x
  binary_iff R x y := by rw [← h]; exact f.binary_iff R x y

def Embedding.sourceCongr {A B : Structure L V} {C : Structure L W}
    (f : Embedding A C) (h : A = B) : Embedding B C where
  point := f.point
  injective := f.injective
  sort_eq x := by rw [← h]; exact f.sort_eq x
  map_func F x y hy := by
    rw [← h] at hy
    exact f.map_func F x y hy
  reflect_func F x y hy := by rw [← h]; exact f.reflect_func F x y hy
  unary_iff U x := by rw [← h]; exact f.unary_iff U x
  binary_iff R x y := by rw [← h]; exact f.binary_iff R x y

theorem ext_data {C D : Structure L V} (hsort : C.sort = D.sort)
    (hfunc : C.func = D.func) (hunary : C.unary = D.unary)
    (hbinary : C.binary = D.binary) : C = D := by
  cases C; cases D
  cases hsort; cases hfunc; cases hunary; cases hbinary
  rfl

/-- A specified induced point map determines every source graph and relation. -/
theorem Embedding.source_eq_of_same_point
    {A B : Structure L V} {C : Structure L W}
    (f : Embedding A C) (g : Embedding B C)
    (same : ∀ x, f.point x = g.point x) : A = B := by
  apply ext_data
  · exact funext fun x => (f.sort_eq x).symm.trans
      ((congrArg C.sort (same x)).trans (g.sort_eq x))
  · apply funext; intro F
    apply funext; intro x
    apply Set.ext; intro y
    constructor
    · intro hy
      have h := f.map_func F x y hy
      rw [same x, same y] at h
      obtain ⟨z, hz, hzy⟩ := g.reflect_func F x (g.point y) h
      exact g.injective hzy ▸ hz
    · intro hy
      have h := g.map_func F x y hy
      rw [← same x, ← same y] at h
      obtain ⟨z, hz, hzy⟩ := f.reflect_func F x (f.point y) h
      exact f.injective hzy ▸ hz
  · apply funext; intro U
    apply funext; intro x
    apply propext
    rw [← f.unary_iff U x, ← g.unary_iff U x, same x]
  · apply funext; intro R
    apply funext; intro x
    apply funext; intro y
    apply propext
    rw [← f.binary_iff R x y, ← g.binary_iff R x y, same x, same y]

/-- Pull the expanded induced structure back along an injective old point
map, ONLY after its image has been proved expanded-closed. -/
def pullback (C : Structure L W) (j : V → W) (hinj : Function.Injective j)
    (_closed : C.IsClosed (Set.range j)) : Structure L V where
  sort x := C.sort (j x)
  func F x := {y | j y ∈ C.func F (j x)}
  functional F x y z hy hz := hinj (C.functional F (j x) (j y) (j z) hy hz)
  func_sorted F x y hy := C.func_sorted F (j x) (j y) hy
  unary U x := C.unary U (j x)
  unary_sorted U x hx := C.unary_sorted U (j x) hx
  binary R x y := C.binary R (j x) (j y)
  binary_sorted R x y hxy := C.binary_sorted R (j x) (j y) hxy

def pullbackEmbedding (C : Structure L W) (j : V → W) (hinj : Function.Injective j)
    (closed : C.IsClosed (Set.range j)) : Embedding (C.pullback j hinj closed) C where
  point := j
  injective := hinj
  sort_eq _ := rfl
  map_func _ _ _ h := h
  reflect_func F x y hy := by
    obtain ⟨z, rfl⟩ := closed F (j x) ⟨x, rfl⟩ hy
    exact ⟨z, hy, rfl⟩
  unary_iff _ _ := Iff.rfl
  binary_iff _ _ _ := Iff.rfl

theorem pullback_reduct_eq (C : Structure L₁ W) (ρ : Reduct L₀ L₁)
    (D : Structure L₀ V) (j : Embedding D (C.reduct ρ))
    (closed : C.IsClosed (Set.range j.point)) :
    (C.pullback j.point j.injective closed).reduct ρ = D :=
  ((C.pullbackEmbedding j.point j.injective closed).reduct ρ).source_eq_of_same_point j
    (fun _ => rfl)

theorem Embedding.root_coordinates_image_subset
    {C : Structure L V} {D : Structure L W} (f : Embedding C D) (S : RootScheme L) :
    f.point '' (Object.full C S).coordinates ⊆ (Object.full D S).coordinates := by
  rintro _ ⟨_, ⟨r, j, rfl⟩, rfl⟩
  exact ⟨r.map f, j, rfl⟩

/-- Every point, rather than only selected source coordinates, lands in
the OLD-root-generated normalization of the target. -/
theorem Embedding.range_subset_oldRootSupport
    {C : Structure L V} {D : Structure L W} (f : Embedding C D) (S : RootScheme L)
    (generated : RootGenerated C S) : Set.range f.point ⊆ oldRootSupport D S := by
  rintro _ ⟨x, rfl⟩
  have hx : f.point x ∈ f.point '' C.closure (Object.full C S).coordinates := by
    refine ⟨x, ?_, rfl⟩
    change x ∈ (Object.full C S).support
    rw [generated]
    trivial
  rw [← f.closure_image] at hx
  exact D.closure_minimal (D.isClosed_closure (Object.full D S).coordinates)
    (fun y hy => D.subset_closure _ (f.root_coordinates_image_subset S hy)) hx

/-- C49--C50: after reasonableness has supplied an ACTUAL expanded inclusion
on the old-normalized carrier, the whole expanded source embedding factors
through the *given* expansion of that carrier.  This uses no favorable
preselected expansion and no closure assertion about every expansion of D. -/
noncomputable def factor_through_old_normalization
    (A : Structure L₁ V) (D : Structure L₁ W) (ρ : Reduct L₀ L₁)
    (S : RootScheme L₀) (generated : RootGenerated (A.reduct ρ) S)
    (D₀ : Structure L₁ (oldRootSupport (D.reduct ρ) S))
    (j : Embedding D₀ D) (marked : ∀ x, j.point x = x.val)
    (f : Embedding A D) : Embedding A D₀ :=
  f.factor j (by
    intro y hy
    have hold : y ∈ oldRootSupport (D.reduct ρ) S :=
      (f.reduct ρ).range_subset_oldRootSupport S generated hy
    exact ⟨⟨y, hold⟩, marked _⟩)

theorem factor_through_old_normalization_comp
    (A : Structure L₁ V) (D : Structure L₁ W) (ρ : Reduct L₀ L₁)
    (S : RootScheme L₀) (generated : RootGenerated (A.reduct ρ) S)
    (D₀ : Structure L₁ (oldRootSupport (D.reduct ρ) S))
    (j : Embedding D₀ D) (marked : ∀ x, j.point x = x.val)
    (f : Embedding A D) :
    j.comp (factor_through_old_normalization A D ρ S generated D₀ j marked f) = f :=
  f.factor_comp j _

end CCO.FullCode.Structure
