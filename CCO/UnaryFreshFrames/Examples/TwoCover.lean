import CCO.UnaryFreshFrames.ClosureActions
import CCO.UnaryFreshFrames.Age
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! C49 second actual model: Q=ℕ, V=Q×Bool with named fibrewise swap,
M=V×ℕ. The named projections are τ:M→V, r:V→Q and p=r∘τ.
Typed root-equality relations add no function or term; they are exactly
same-root tests determined by these named projections on closed pieces. -/
namespace CCO.UnaryFreshFrames.Examples.TwoCover
open Structure

abbrev Point := ((ℕ × Bool) × ℕ) ⊕ ((ℕ × Bool) ⊕ ℕ)
def real (q : ℕ) (b : Bool) (n : ℕ) : Point := .inl ((q,b),n)
def middle (q : ℕ) (b : Bool) : Point := .inr (.inl (q,b))
def rootPoint (q : ℕ) : Point := .inr (.inr q)

def sort : Point → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def root : Point → ℕ
  | .inl ((q,_),_) => q
  | .inr (.inl (q,_)) => q
  | .inr (.inr q) => q

def bit : Point → Bool
  | .inl ((_,b),_) => b
  | .inr (.inl (_,b)) => b
  | .inr (.inr _) => false

def coordinate : Point → ℕ
  | .inl (_,n) => n
  | .inr _ => 0

abbrev language : Language where
  Sorts := Fin 3
  Func := Fin 4
  Rel := Fin 3 × Fin 3
  input F := if F = 0 ∨ F = 2 then 0 else 1
  output F := if F = 0 ∨ F = 3 then 1 else 2
  arity _ := 2
  argument R i := if i = 0 then R.1 else R.2

def operation (F : Fin 4) : Point → Point
  | .inl ((q,b),n) => if F = 0 then middle q b else if F = 2 then rootPoint q else real q b n
  | .inr (.inl (q,b)) => if F = 1 then rootPoint q else if F = 3 then middle q (!b) else middle q b
  | .inr (.inr q) => rootPoint q

def model : Structure language Point where
  sort := sort
  func := operation
  func_sort := by
    intro F x hx
    rcases x with ⟨⟨q,b⟩,n⟩ | (⟨q,b⟩ | q)
    all_goals fin_cases F <;> simp_all [language,sort,operation,middle,rootPoint]
  func_offsort := by
    intro F x hx
    rcases x with ⟨⟨q,b⟩,n⟩ | (⟨q,b⟩ | q)
    all_goals fin_cases F <;> simp_all [language,sort,operation,real,middle,rootPoint]
  rel R xs := sort (xs 0) = R.1 ∧ sort (xs 1) = R.2 ∧ root (xs 0) = root (xs 1)
  rel_sort := by
    intro R xs h i
    fin_cases i
    · exact h.1
    · exact h.2.1

theorem point_ext {x y : Point} (hs : sort x = sort y) (hr : root x = root y)
    (hb : sort x ≠ 2 → bit x = bit y)
    (hn : sort x = 0 → coordinate x = coordinate y) : x = y := by
  rcases x with ⟨⟨q,b⟩,n⟩ | (⟨q,b⟩ | q)
  all_goals rcases y with ⟨⟨r,c⟩,m⟩ | (⟨r,c⟩ | r)
  all_goals simp [sort,root,bit,coordinate] at hs hr hb hn ⊢
  all_goals simp_all

theorem singleton_root_closed (q : ℕ) : model.Closed {rootPoint q} := by
  intro F x hx
  have he : x = rootPoint q := hx
  subst x
  rfl

theorem root_closure (q : ℕ) : model.closureAt (rootPoint q) = {rootPoint q} :=
  model.closure_eq (singleton_root_closed q)

theorem middle_closure (q : ℕ) (b : Bool) :
    model.closureAt (middle q b) = {middle q b, middle q (!b), rootPoint q} := by
  apply Set.Subset.antisymm
  · apply model.closure_minimal
    · intro F x hx
      rcases hx with rfl | rfl | rfl
      all_goals fin_cases F <;> simp [model,operation,middle,rootPoint,Bool.not_not]
    · exact Set.singleton_subset_iff.mpr (Or.inl rfl)
  · intro x hx
    rcases hx with rfl | rfl | rfl
    · exact model.subset_closure _ rfl
    · exact model.closure_closed {middle q b} 3 (middle q b) (model.subset_closure _ rfl)
    · exact model.closure_closed {middle q b} 1 (middle q b) (model.subset_closure _ rfl)

theorem real_closure (q : ℕ) (b : Bool) (n : ℕ) :
    model.closureAt (real q b n) =
      {real q b n, middle q b, middle q (!b), rootPoint q} := by
  apply Set.Subset.antisymm
  · apply model.closure_minimal
    · intro F x hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals fin_cases F <;> simp [model,operation,real,middle,rootPoint,Bool.not_not]
    · exact Set.singleton_subset_iff.mpr (Or.inl rfl)
  · intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact model.subset_closure _ rfl
    · exact model.closure_closed {real q b n} 0 (real q b n) (model.subset_closure _ rfl)
    · exact model.closure_closed {real q b n} 3 (middle q b)
        (model.closure_closed {real q b n} 0 (real q b n) (model.subset_closure _ rfl))
    · exact model.closure_closed {real q b n} 2 (real q b n) (model.subset_closure _ rfl)

theorem middle_off_root_closure (q : ℕ) (b : Bool) :
    middle q b ∉ model.closureAt (rootPoint q) := by
  rw [root_closure]
  simp [middle,rootPoint]

/-- The literal τ-image of the actual p-fibre is exactly TWO points. -/
theorem actual_fibre_image (q : ℕ) :
    operation 0 '' {x : Point | sort x = 0 ∧ operation 2 x = rootPoint q} =
      {middle q false, middle q true} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx,hp⟩, rfl⟩
    rcases x with ⟨⟨r,b⟩,n⟩ | (⟨r,b⟩ | r)
    · have hr : r = q := by simpa [operation,real,rootPoint] using hp
      subst r
      cases b <;> simp [operation,middle]
    · simp [sort] at hx
    · simp [sort] at hx
  · rintro (rfl | rfl)
    · exact ⟨real q false 0, ⟨rfl,rfl⟩, rfl⟩
    · exact ⟨real q true 0, ⟨rfl,rfl⟩, rfl⟩

/-- This is the actual finite proper relative index, not a formal ratio. -/
theorem actual_relative_index_two (q : ℕ) :
    (operation 0 '' {x : Point | sort x = 0 ∧ operation 2 x = rootPoint q}).ncard = 2 := by
  rw [actual_fibre_image]
  simp [middle]

end CCO.UnaryFreshFrames.Examples.TwoCover
