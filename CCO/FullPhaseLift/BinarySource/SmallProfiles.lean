import CCO.FullPhaseLift.Canonical.Signature
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Complete two-slot profiles determine EVERY relation tuple of support
at most two, even when its arity is large or zero. This is the literal
compatibility check needed by the chosen-pair full lifting interface. -/

universe u v
namespace CCO.FullPhaseLift.BinarySource
open Canonical
noncomputable section

theorem small_truth_of_pair_profiles {L : Signature} {M : Type u} {V : Type v}
    (U : BoolTable L M) (p q : V → M)
    (pairs : ∀ x y, profile U ![p x,p y] = profile U ![q x,q y])
    (r : Fin L.size) (xs : Fin (L.arity r) → V)
    (small : ∀ i j k, xs i = xs j ∨ xs i = xs k ∨ xs j = xs k) :
    U r (p ∘ xs) = U r (q ∘ xs) := by
  classical
  by_cases hzero : L.arity r = 0
  · have htuple : p ∘ xs = q ∘ xs := by
      funext i
      have hi : Fin 0 := Fin.cast hzero i
      exact Fin.elim0 hi
    rw [htuple]
  · have hpos : 0 < L.arity r := Nat.pos_of_ne_zero hzero
    let i₀ : Fin (L.arity r) := ⟨0,hpos⟩
    by_cases hsingle : ∀ i, xs i = xs i₀
    · let test : AtomicTest L 2 := ⟨r,fun _ => 0⟩
      have h := congrFun (pairs (xs i₀) (xs i₀)) test
      have hp : ![p (xs i₀),p (xs i₀)] ∘ (fun _ : Fin (L.arity r) => (0 : Fin 2)) = p ∘ xs := by
        funext i
        exact congrArg p (hsingle i).symm
      have hq : ![q (xs i₀),q (xs i₀)] ∘ (fun _ : Fin (L.arity r) => (0 : Fin 2)) = q ∘ xs := by
        funext i
        exact congrArg q (hsingle i).symm
      change U r (![p (xs i₀),p (xs i₀)] ∘ (fun _ => 0)) =
        U r (![q (xs i₀),q (xs i₀)] ∘ (fun _ => 0)) at h
      rwa [hp,hq] at h
    · obtain ⟨i₁,hi₁⟩ := not_forall.mp hsingle
      let tag : Fin (L.arity r) → Fin 2 := fun i => if xs i = xs i₀ then 0 else 1
      have htag (i : Fin (L.arity r)) : ![xs i₀,xs i₁] (tag i) = xs i := by
        by_cases hi : xs i = xs i₀
        · simp only [tag,if_pos hi,Matrix.cons_val_zero]
          exact hi.symm
        · have he : xs i = xs i₁ := by
            rcases small i i₀ i₁ with he | he | he
            · exact (hi he).elim
            · exact he
            · exact (hi₁ he.symm).elim
          simp only [tag,if_neg hi,Matrix.cons_val_one,Matrix.cons_val_zero]
          exact he.symm
      have hp : ![p (xs i₀),p (xs i₁)] ∘ tag = p ∘ xs := by
        funext i
        change ![p (xs i₀),p (xs i₁)] (tag i) = p (xs i)
        rw [← htag i]
        generalize tag i = j
        fin_cases j <;> rfl
      have hq : ![q (xs i₀),q (xs i₁)] ∘ tag = q ∘ xs := by
        funext i
        change ![q (xs i₀),q (xs i₁)] (tag i) = q (xs i)
        rw [← htag i]
        generalize tag i = j
        fin_cases j <;> rfl
      have h := congrFun (pairs (xs i₀) (xs i₁)) (⟨r,tag⟩ : AtomicTest L 2)
      change U r (![p (xs i₀),p (xs i₁)] ∘ tag) = U r (![q (xs i₀),q (xs i₁)] ∘ tag) at h
      rwa [hp,hq] at h

end
end CCO.FullPhaseLift.BinarySource
