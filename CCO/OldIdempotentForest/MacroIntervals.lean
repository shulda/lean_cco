import CCO.OldIdempotentForest.ProfileSemigroup
import Mathlib.Data.List.Chain
import Mathlib.Data.List.FinRange

/-! Nonempty evaluation, genuine composability and every contiguous
original macro interval. Original words and occurrence indices remain
data; profiles alone never choose replacement branch words. -/

universe u v w r a
namespace CCO.OldIdempotentForest
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

/-- Empty input has the absorbing zero value. Nonempty inputs use a
positive semigroup fold, never a fold starting from zero. -/
def profileEval {A : Type a} (letter : A → TypedProfileState S) :
    List A → TypedProfileState S
  | [] => .zero
  | [x] => letter x
  | x :: y :: tail => profileMul S H sap (letter x) (profileEval letter (y :: tail))

@[simp] theorem profileEval_nil {A : Type a} (letter : A → TypedProfileState S) :
    profileEval S H sap letter [] = .zero := rfl
@[simp] theorem profileEval_singleton {A : Type a} (letter : A → TypedProfileState S) (x : A) :
    profileEval S H sap letter [x] = letter x := rfl

theorem profileEval_cons_of_ne {A : Type a} (letter : A → TypedProfileState S)
    (x : A) (tail : List A) (ht : tail ≠ []) :
    profileEval S H sap letter (x :: tail) =
      profileMul S H sap (letter x) (profileEval S H sap letter tail) := by
  cases tail with
  | nil => exact False.elim (ht rfl)
  | cons y rest => rfl

theorem profileEval_append {A : Type a} (letter : A → TypedProfileState S)
    (left right : List A) (hl : left ≠ []) (hr : right ≠ []) :
    profileEval S H sap letter (left ++ right) =
      profileMul S H sap (profileEval S H sap letter left) (profileEval S H sap letter right) := by
  induction left with
  | nil => exact False.elim (hl rfl)
  | cons x tail ih =>
    cases tail with
    | nil =>
      cases right with
      | nil => exact False.elim (hr rfl)
      | cons y rest => rfl
    | cons y rest =>
      simp only [List.cons_append,profileEval]
      have ht : profileEval S H sap letter (y :: (rest ++ right)) =
          profileMul S H sap (profileEval S H sap letter (y :: rest))
            (profileEval S H sap letter right) := ih (List.cons_ne_nil _ _)
      rw [ht,profileMul_assoc]

theorem profileEval_map {A : Type a} {B : Type*} (f : A → B)
    (letter : B → TypedProfileState S) (word : List A) :
    profileEval S H sap letter (word.map f) =
      profileEval S H sap (letter ∘ f) word := by
  induction word with
  | nil => rfl
  | cons x tail ih =>
    cases tail with
    | nil => rfl
    | cons y rest =>
      simp only [List.map_cons,profileEval,Function.comp_apply]
      exact congrArg (profileMul S H sap (letter (f x))) ih

/-- Every positive composable list evaluates to an ACTUAL positive
reachable profile, retaining the literal initial and final sort tags. -/
theorem positive_chain_evaluation (word : List (ReachableProfile S))
    (hne : word ≠ []) (hcomp : word.IsChain ReachableProfile.Compatible) :
    ∃ p : ReachableProfile S,
      profileEval S H sap TypedProfileState.positive word = .positive p ∧
      p.source = (word.head hne).source ∧ p.target = (word.getLast hne).target := by
  induction word with
  | nil => exact False.elim (hne rfl)
  | cons p tail ih =>
    cases tail with
    | nil => exact ⟨p,rfl,rfl,rfl⟩
    | cons q tail =>
      have hc := List.isChain_cons_cons.mp hcomp
      obtain ⟨t,he,hs,ht⟩ := ih (List.cons_ne_nil _ _) hc.2
      have hpt : p.Compatible t := hc.1.trans hs.symm
      refine ⟨composeReachable S H sap p t hpt,?_,?_,?_⟩
      · change profileMul S H sap (.positive p)
          (profileEval S H sap TypedProfileState.positive (q :: tail)) = _
        rw [he,profileMul_compatible]
      · exact composeReachable_source S H sap p t hpt
      · exact (composeReachable_target S H sap p t hpt).trans ht

theorem positive_chain_nonzero (word : List (ReachableProfile S))
    (hne : word ≠ []) (hcomp : word.IsChain ReachableProfile.Compatible) :
    profileEval S H sap TypedProfileState.positive word ≠ .zero := by
  obtain ⟨p,hp,_,_⟩ := positive_chain_evaluation S H sap word hne hcomp
  rw [hp]
  exact TypedProfileState.positive_ne_zero p

/-- Only contiguous deletion preserves a typed composability chain.
This proof deliberately uses drop/take rather than arbitrary sublists. -/
theorem positive_interval_nonzero (word : List (ReachableProfile S))
    (hcomp : word.IsChain ReachableProfile.Compatible)
    (lo hi : ℕ) (hlo : lo < hi) (hhi : hi ≤ word.length) :
    profileEval S H sap TypedProfileState.positive ((word.drop lo).take (hi-lo)) ≠ .zero := by
  apply positive_chain_nonzero
  · intro he
    have hlen := congrArg List.length he
    simp only [List.length_take,List.length_drop,List.length_nil] at hlen
    omega
  · exact (hcomp.drop lo).take (hi-lo)

/-- An actual indexed macro path retains its EXACT traversed positive
word at every occurrence. Old source roots are added by the source adapter. -/
structure MacroPath (n : ℕ) where
  sort : Fin (n+1) → ι
  word : ∀ k : Fin n, PositiveWord S (sort k.castSucc) (sort k.succ)

namespace MacroPath
variable {S} {n : ℕ} (P : MacroPath S n)

def letter (k : Fin n) : ReachableProfile S := wordProfile S H sap (P.word k)
def letters : List (ReachableProfile S) := (List.finRange n).map (P.letter H sap)
def eval : List (Fin n) → TypedProfileState S :=
  profileEval S H sap (fun k => .positive (P.letter H sap k))

theorem letters_composable : (P.letters H sap).IsChain ReachableProfile.Compatible := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi' : i+1 < n := by simpa only [letters,List.length_map,List.length_finRange] using hi
  simp only [letters,List.getElem_map,List.getElem_finRange]
  change P.sort _ = P.sort _
  congr 1

theorem eval_append (left right : List (Fin n)) (hl : left ≠ []) (hr : right ≠ []) :
    P.eval H sap (left ++ right) =
      profileMul S H sap (P.eval H sap left) (P.eval H sap right) :=
  profileEval_append S H sap _ left right hl hr

theorem eval_interval_nonzero (lo hi : ℕ) (hlo : lo < hi) (hhi : hi ≤ n) :
    P.eval H sap (((List.finRange n).drop lo).take (hi-lo)) ≠ .zero := by
  have h := positive_interval_nonzero S H sap (P.letters H sap)
    (P.letters_composable H sap) lo hi hlo
    (by simpa only [letters,List.length_map,List.length_finRange] using hhi)
  have hs : ((P.letters H sap).drop lo).take (hi-lo) =
      ((((List.finRange n).drop lo).take (hi-lo)).map (P.letter H sap)) := by
    simp only [letters,List.map_take,List.map_drop]
  rw [hs,profileEval_map] at h
  exact h

theorem eval_nonzero (hn : 0 < n) : P.eval H sap (List.finRange n) ≠ .zero := by
  have h := P.eval_interval_nonzero H sap 0 n hn (le_refl n)
  have ht : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  simpa only [List.drop_zero,Nat.sub_zero,ht] using h

end MacroPath
end
end CCO.OldIdempotentForest
