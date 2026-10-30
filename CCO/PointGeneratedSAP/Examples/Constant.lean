import CCO.PointGeneratedSAP.Examples.Matching

/-! A hidden singleton supplied by a UNARY constant map, with no nullary
symbol. Nonempty real bases conceal precisely the empty-base obstruction. -/
namespace CCO.PointGeneratedSAP.Examples.Constant
open UnaryFreshFrames UnaryFreshFrames.Structure

abbrev Point := Option ℕ
def real (n : ℕ) : Point := some n
def hidden : Point := none

def sort : Point → Bool
  | some _ => false
  | none => true

abbrev language : Language where
  Sorts := Bool
  Func := Unit
  Rel := Empty
  input _ := false
  output _ := true
  arity := Empty.elim
  argument := fun r => Empty.elim r

def model : Structure language Point where
  sort := sort
  func _ _ := hidden
  func_sort _ _ _ := rfl
  func_offsort := by
    rintro _ (n | n) hn
    · rfl
    · exact False.elim (hn rfl)
  rel := fun r => Empty.elim r
  rel_sort := fun r => Empty.elim r

def points (D : Set ℕ) : Set Point :=
  {x | (∃ n ∈ D, x = real n) ∨ x = hidden ∧ D.Nonempty}

theorem closure_reals (D : Set ℕ) : model.closure (real '' D) = points D := by
  apply Set.Subset.antisymm
  · apply model.closure_minimal
    · rintro F x (⟨n,hn,rfl⟩ | ⟨rfl,n,hn⟩)
      · exact Or.inr ⟨rfl,n,hn⟩
      · exact Or.inr ⟨rfl,n,hn⟩
    · rintro _ ⟨n,hn,rfl⟩
      exact Or.inl ⟨n,hn,rfl⟩
  · rintro x (⟨n,hn,rfl⟩ | ⟨rfl,n,hn⟩)
    · exact model.subset_closure _ ⟨n,hn,rfl⟩
    · exact model.closure_closed _ () (real n) (model.subset_closure _ ⟨n,hn,rfl⟩)

theorem closure_reals_finite {D : Set ℕ} (hD : D.Finite) :
    (model.closure (real '' D)).Finite := by
  rw [closure_reals]
  apply ((hD.image real).union (Set.finite_singleton hidden)).subset
  rintro x (⟨n,hn,rfl⟩ | ⟨rfl,_⟩)
  · exact Or.inl ⟨n,hn,rfl⟩
  · exact Or.inr rfl

def permAut (p : Equiv.Perm ℕ) : model.Aut := by
  refine ⟨Equiv.optionCongr p,?_,fun _ _ => rfl,?_⟩
  · rintro (n | n) <;> rfl
  · intro r
    exact Empty.elim r

@[simp] theorem permAut_real (p : Equiv.Perm ℕ) (n : ℕ) :
    permAut p • real n = real (p n) := rfl

@[simp] theorem permAut_hidden (p : Equiv.Perm ℕ) : permAut p • hidden = hidden := rfl

theorem hidden_fixed (g : model.Aut) : g • hidden = hidden :=
  model.aut_func g () (real 0)

theorem hidden_in_nonempty_closure {D : Set ℕ} (hD : D.Nonempty) :
    hidden ∈ model.closure (real '' D) := by
  rw [closure_reals]
  exact Or.inr ⟨rfl,hD⟩

/-- Every nonempty real base passes the off-closure orbit test. The empty
base is intentionally excluded here and fails immediately below. -/
theorem nonempty_real_base_orbits (D : Set ℕ) (hD : D.Finite) (hne : D.Nonempty)
    (x : Point) (hx : x ∉ model.closure (real '' D)) :
    (orbitOver model.Aut (real '' D) x).Infinite := by
  classical
  cases x with
  | none => exact False.elim (hx (hidden_in_nonempty_closure hne))
  | some n =>
    intro hf
    let index : Point → ℕ := fun x => x.getD 0
    obtain ⟨k,_,hk⟩ := (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finite
      (hD.union (hf.image index))
    have hn : n ∉ D := fun hn => hx (model.subset_closure _ ⟨n,hn,rfl⟩)
    let g := permAut (Equiv.swap n k)
    have hfix : ∀ a ∈ real '' D, g • a = a := by
      rintro _ ⟨m,hm,rfl⟩
      change real (Equiv.swap n k m) = real m
      rw [Equiv.swap_apply_of_ne_of_ne (fun he : m = n => hn (he ▸ hm))
        (fun he : m = k => hk (Or.inl (he ▸ hm)))]
    have hmove : g • real n = real k := by simp [g]
    have hm : real k ∈ orbitOver model.Aut (real '' D) (real n) :=
      (mem_orbitOver_iff model.Aut).mpr ⟨g,hfix,hmove⟩
    exact hk (Or.inr ⟨real k,hm,rfl⟩)

theorem hidden_empty_orbit : orbitOver model.Aut ∅ hidden = {hidden} := by
  apply Set.Subset.antisymm
  · rintro x ⟨g,rfl⟩
    exact hidden_fixed g.val
  · rintro x rfl
    exact ⟨1,one_smul _ _⟩

theorem empty_base_failure : hidden ∉ model.closure ∅ ∧
    (orbitOver model.Aut ∅ hidden).Finite := by
  constructor
  · rw [model.closure_empty]
    exact Set.notMem_empty _
  · rw [hidden_empty_orbit]
    exact Set.finite_singleton _

def pair : model.Piece where
  points := {real 0,hidden}
  finite := (Set.finite_singleton _).insert _
  closed := by
    rintro F x hx
    exact Or.inr rfl

theorem pair_point_generated : pair.points = model.closure (real '' ({0} : Set ℕ)) := by
  rw [closure_reals]
  ext x
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl ⟨0,rfl,rfl⟩
    · exact Or.inr ⟨rfl,0,rfl⟩
  · rintro (⟨n,rfl,rfl⟩ | ⟨rfl,_⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem hidden_embedding_fixed {D : model.Piece} (f : pair.Embedding D.points) :
    f.point ⟨hidden,Or.inr rfl⟩ = hidden := by
  have h := f.func_eq () ⟨real 0,Or.inl rfl⟩
  exact h

/-- No two copies of this point-generated pair can have disjoint images
in ANY actual induced finite target. Thus SAP over the empty base fails. -/
theorem no_empty_base_strong_amalgam :
    ¬ ∃ (D : model.Piece) (l r : pair.Embedding D.points),
      ∀ x y, l.point x ≠ r.point y := by
  rintro ⟨D,l,r,h⟩
  exact h ⟨hidden,Or.inr rfl⟩ ⟨hidden,Or.inr rfl⟩
    ((hidden_embedding_fixed l).trans (hidden_embedding_fixed r).symm)

end CCO.PointGeneratedSAP.Examples.Constant
