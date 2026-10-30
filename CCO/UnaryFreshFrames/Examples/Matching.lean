import CCO.UnaryFreshFrames.ClosureActions
import CCO.UnaryFreshFrames.Age
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases

/-! C49, first countable model: M = Q × ℕ, a matching copy S of Q,
named p:M→Q and τ:M→S, with no unary map out of Q or S. The finite
family of typed root relations is a conservative relational presentation:
on closed pieces every instance is an equality of p/τ values or the
Q–S matching relation. No extra function or term is introduced. -/
namespace CCO.UnaryFreshFrames.Examples.Matching
open Structure

abbrev Point := (ℕ × ℕ) ⊕ (ℕ ⊕ ℕ)
def real (q n : ℕ) : Point := Sum.inl (q,n)
def rootPoint (q : ℕ) : Point := Sum.inr (Sum.inl q)
def partner (q : ℕ) : Point := Sum.inr (Sum.inr q)

def sort : Point → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def root : Point → ℕ
  | .inl p => p.1
  | .inr (.inl q) => q
  | .inr (.inr q) => q

def coordinate : Point → ℕ
  | .inl p => p.2
  | .inr _ => 0

abbrev language : Language where
  Sorts := Fin 3
  Func := Bool
  Rel := Fin 3 × Fin 3
  input _ := 0
  output F := if F then 2 else 1
  arity _ := 2
  argument R i := if i = 0 then R.1 else R.2

def operation (F : Bool) : Point → Point
  | .inl p => if F then partner p.1 else rootPoint p.1
  | .inr p => .inr p

def model : Structure language Point where
  sort := sort
  func := operation
  func_sort := by
    intro F x hx
    rcases x with ⟨q,n⟩ | (q | q)
    · cases F <;> rfl
    · simp [sort, language] at hx
    · simp [sort, language] at hx
  func_offsort := by
    intro F x hx
    rcases x with ⟨q,n⟩ | (q | q)
    · exact False.elim (hx rfl)
    · rfl
    · rfl
  rel R xs := sort (xs 0) = R.1 ∧ sort (xs 1) = R.2 ∧ root (xs 0) = root (xs 1)
  rel_sort := by
    intro R xs h i
    fin_cases i
    · exact h.1
    · exact h.2.1

theorem point_ext {x y : Point} (hs : sort x = sort y) (hr : root x = root y)
    (hn : sort x = 0 → coordinate x = coordinate y) : x = y := by
  rcases x with ⟨q,n⟩ | (q | q)
  all_goals rcases y with ⟨r,m⟩ | (r | r)
  all_goals simp [sort,root,coordinate] at hs hr hn ⊢
  all_goals simp_all

theorem term_nonreal {i j : language.Sorts} (hi : i ≠ 0) (t : Term language i j) :
    i = j ∧ ∀ x, model.eval t x = x := by
  induction t with
  | id => exact ⟨rfl,fun _ => rfl⟩
  | func F t ih => exact False.elim (hi ih.1)

theorem no_named_factor : ¬ Nonempty (Term language 1 2) := by
  rintro ⟨t⟩
  have h := (term_nonreal (i := 1) (by decide) t).1
  exact (by decide : (1 : Fin 3) ≠ 2) h

theorem singleton_root_closed (q : ℕ) : model.Closed {rootPoint q} := by
  intro F x hx
  have he : x = rootPoint q := hx
  subst x
  rfl

theorem root_closure (q : ℕ) : model.closureAt (rootPoint q) = {rootPoint q} :=
  model.closure_eq (singleton_root_closed q)

theorem partner_off_closure (q : ℕ) : partner q ∉ model.closureAt (rootPoint q) := by
  rw [root_closure]
  simp [partner,rootPoint]

theorem real_closure (q n : ℕ) :
    model.closureAt (real q n) = {real q n, rootPoint q, partner q} := by
  apply Set.Subset.antisymm
  · apply model.closure_minimal
    · intro F x hx
      rcases hx with rfl | rfl | rfl
      · cases F <;> simp [model,operation,real,rootPoint,partner]
      · simp [model,operation,real,rootPoint,partner]
      · simp [model,operation,real,rootPoint,partner]
    · exact Set.singleton_subset_iff.mpr (Or.inl rfl)
  · intro x hx
    rcases hx with rfl | rfl | rfl
    · exact model.subset_closure _ rfl
    · exact model.closure_closed {real q n} false (real q n) (model.subset_closure _ rfl)
    · exact model.closure_closed {real q n} true (real q n) (model.subset_closure _ rfl)

/-- The literal matching partner is fixed by EVERY full automorphism over q,
although there is no named term Q→S and it is outside the actual closure. -/
theorem partner_fixed (q : ℕ) (g : model.Aut) (hg : g • rootPoint q = rootPoint q) :
    g • partner q = partner q := by
  have hs : sort (g • partner q) = 2 := model.aut_sort g (partner q)
  have hm : model.rel (1,2) ![rootPoint q,partner q] := by
    exact ⟨rfl,rfl,rfl⟩
  have hm' := (model.aut_rel g (1,2) ![rootPoint q,partner q]).mpr hm
  change sort (g • rootPoint q) = 1 ∧ sort (g • partner q) = 2 ∧
    root (g • rootPoint q) = root (g • partner q) at hm'
  rw [hg] at hm'
  apply point_ext hs
  · exact hm'.2.2.symm
  · intro h
    exact False.elim ((by decide : (2 : Fin 3) ≠ 0) (hs.symm.trans h))

theorem definable_off_closure (q : ℕ) :
    partner q ∈ Dcl model.Aut {rootPoint q} ∧ partner q ∉ model.closureAt (rootPoint q) := by
  refine ⟨?_,partner_off_closure q⟩
  intro g
  exact partner_fixed q g.val (g.property (rootPoint q) rfl)

/-- The typed root predicates are explicitly determined by p, τ, equality
and the Q–S matching. The root equality presentation adds no unary factor. -/
theorem root_formulas (q r n m : ℕ) :
    (root (real q n) = root (real r m) ↔ operation false (real q n) = operation false (real r m)) ∧
    (root (real q n) = root (rootPoint r) ↔ operation false (real q n) = rootPoint r) ∧
    (root (real q n) = root (partner r) ↔ operation true (real q n) = partner r) ∧
    (root (rootPoint q) = root (partner r) ↔ model.rel (1,2) ![rootPoint q,partner r]) := by
  simp [root,real,partner,rootPoint,operation,model,sort]

end CCO.UnaryFreshFrames.Examples.Matching
