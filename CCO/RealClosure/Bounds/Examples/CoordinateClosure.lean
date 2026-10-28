import CCO.RealClosure.Bounds.Examples.CoordinateDirections
import CCO.RealClosure.Bounds.Algebraicity
import Mathlib.Data.Fintype.Pi

/-! Exact actual finite-base orbits: the fixed and finite-orbit sets are the
Cartesian products of represented coordinate values. Outside them, explicit
fresh coordinate swaps embed Nat into the actual stabilizer orbit. -/
universe u
namespace CCO.RealClosure.Bounds.Examples.Coordinate
variable (I : Type u) [Fintype I] [DecidableEq I]

def values (A : Finset (Point I)) (i : I) : Finset ℕ := A.image (fun x => x i)
def grid (A : Finset (Point I)) : Set (Point I) := {x | ∀ i, x i ∈ values I A i}

theorem grid_fixed (A : Finset (Point I)) {x : Point I} (hx : x ∈ grid I A) :
    x ∈ Dcl (Aut I) A := by
  intro g hg
  funext i
  obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp (hx i)
  have hc := (coordinates_of_colour_eq I (g.property x a) i).mpr hax.symm
  change (g • x) i = (g • a) i at hc
  rw [hg a ha] at hc
  exact hc.trans hax

/-- One genuinely infinite orbit, using only finite support permutations. -/
noncomputable def outsideOrbitEmbedding (A : Finset (Point I)) (x : Point I)
    (i : I) (hi : x i ∉ values I A i) : ℕ ↪ orbitOver (Aut I) A x := by
  classical
  let N := max ((values I A i).sup id) (x i) + 1
  have hfresh (n : ℕ) : N+n ∉ values I A i := by
    intro hn
    have hh : N+n ≤ (values I A i).sup id := Finset.le_sup (f := id) hn
    have hmax : (values I A i).sup id ≤ max ((values I A i).sup id) (x i) := Nat.le_max_left _ _
    omega
  let g (n : ℕ) : Aut I := coordinateAut I (fun j =>
    if j = i then Equiv.swap (x i) (N+n) else 1)
  have hfix (n : ℕ) : ∀ a ∈ A, g n • a = a := by
    intro a ha
    funext j
    have hai : a i ∈ values I A i := Finset.mem_image.mpr ⟨a,ha,rfl⟩
    have hxi : a i ≠ x i := fun he => hi (he ▸ hai)
    have hni : a i ≠ N+n := fun he => hfresh n (he ▸ hai)
    change (if j = i then Equiv.swap (x i) (N+n) else 1) (a j) = a j
    by_cases hji : j = i
    · subst j
      simpa using Equiv.swap_apply_of_ne_of_ne hxi hni
    · simp [hji]
  refine ⟨fun n => ⟨g n • x,⟨g n,hfix n,rfl⟩⟩,?_⟩
  intro n m he
  have hh := congrArg (fun p : orbitOver (Aut I) A x => p.val i) he
  change (if i = i then Equiv.swap (x i) (N+n) else 1) (x i) =
    (if i = i then Equiv.swap (x i) (N+m) else 1) (x i) at hh
  simp only [ite_true,Equiv.swap_apply_left] at hh
  exact Nat.add_left_cancel hh

theorem acl_eq_grid (A : Finset (Point I)) : Acl (Aut I) A = grid I A := by
  classical
  ext x
  constructor
  · intro hx
    intro i
    by_contra hi
    letI : Finite (orbitOver (Aut I) A x) := hx.to_subtype
    have hnat : Finite ℕ := Finite.of_injective (outsideOrbitEmbedding I A x i hi)
      (outsideOrbitEmbedding I A x i hi).injective
    letI := hnat
    exact not_finite ℕ
  · intro hx
    have hfixed := grid_fixed I A hx
    apply Set.Finite.subset (Set.finite_singleton x)
    rintro y ⟨g,hg,rfl⟩
    exact Set.mem_singleton_iff.mpr (hfixed g hg)

theorem dcl_eq_grid (A : Finset (Point I)) : Dcl (Aut I) A = grid I A := by
  apply Set.Subset.antisymm
  · intro x hx
    have hfin : x ∈ Acl (Aut I) A := by
      apply Set.Finite.subset (Set.finite_singleton x)
      rintro y ⟨g,hg,rfl⟩
      exact Set.mem_singleton_iff.mpr (hx g hg)
    rwa [acl_eq_grid] at hfin
  · exact fun _ hx => grid_fixed I A hx

noncomputable def gridEquiv (A : Finset (Point I)) :
    grid I A ≃ (∀ i : I, ↥(values I A i)) where
  toFun x i := ⟨x.val i,x.property i⟩
  invFun f := ⟨fun i => (f i).val,fun i => (f i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem grid_finite (A : Finset (Point I)) : (grid I A).Finite := by
  classical
  exact Set.finite_coe_iff.mp (Finite.of_injective (gridEquiv I A) (gridEquiv I A).injective)

/-- The literal n-point diagonal base. -/
def diagonal (n : ℕ) : Finset (Point I) := (Finset.range n).image (fun k => fun _ => k)

@[simp] theorem values_diagonal (n : ℕ) (i : I) : values I (diagonal I n) i = Finset.range n := by
  ext k
  simp only [values,diagonal,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨x,⟨j,hj,rfl⟩,rfl⟩
    exact hj
  · intro hk
    exact ⟨fun _ => k,⟨k,hk,rfl⟩,rfl⟩

noncomputable def diagonalGridEquiv (n : ℕ) : grid I (diagonal I n) ≃ (I → Fin n) where
  toFun x i := ⟨x.val i,by
    have hh := x.property i
    rw [values_diagonal] at hh
    exact Finset.mem_range.mp hh⟩
  invFun f := ⟨fun i => (f i).val,fun i => by
    rw [values_diagonal]
    exact Finset.mem_range.mpr (f i).isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem diagonal_closure_card (n : ℕ) :
    Nat.card (Acl (Aut I) (diagonal I n)) = n^(Nat.card I) ∧
    Nat.card (Dcl (Aut I) (diagonal I n)) = n^(Nat.card I) := by
  rw [acl_eq_grid,dcl_eq_grid]
  have hh := Nat.card_congr (diagonalGridEquiv I n)
  simp only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin] at hh ⊢
  exact ⟨hh,hh⟩

theorem diagonal_card [Nonempty I] (n : ℕ) : (diagonal I n).card = n := by
  classical
  rw [diagonal,Finset.card_image_of_injective]
  · exact Finset.card_range n
  · intro n m h
    obtain ⟨i⟩ := ‹Nonempty I›
    exact congrFun h i
end CCO.RealClosure.Bounds.Examples.Coordinate
