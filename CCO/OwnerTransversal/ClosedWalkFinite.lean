import CCO.OwnerTransversal.ClosedWalk
import Mathlib.Data.List.OfFn

universe v w t
namespace CCO.OwnerTransversal

variable {M : Type v}

/-- A represented finite product records every intermediate point. -/
theorem product_ofFn_iff (n : Nat) (R : Fin n → Relation M) (x y : M) :
    relationProduct (List.ofFn R) x y ↔
      ∃ p : Fin (n+1) → M, p 0 = x ∧ p (Fin.last n) = y ∧
        ∀ k : Fin n, R k (p k.castSucc) (p k.succ) := by
  induction n generalizing x y with
  | zero =>
      simp only [List.ofFn_zero, relationProduct]
      constructor
      · intro h
        subst y
        exact ⟨fun _ => x,rfl,rfl,fun k => Fin.elim0 k⟩
      · rintro ⟨p,hx,hy,_⟩
        exact hx.symm.trans hy
  | succ n ih =>
      rw [List.ofFn_succ]
      change (∃ z, R 0 x z ∧ relationProduct (List.ofFn (fun k => R k.succ)) z y) ↔ _
      constructor
      · rintro ⟨z,hxz,hzy⟩
        obtain ⟨q,hq0,hqLast,hq⟩ := (ih (fun k => R k.succ) z y).mp hzy
        refine ⟨Fin.cases x q,rfl,?_,?_⟩
        · change q (Fin.last n) = y
          exact hqLast
        · intro k
          refine Fin.cases ?_ (fun j => ?_) k
          · change R 0 x (q 0)
            rwa [hq0]
          · simpa only [Fin.castSucc_succ, Fin.cases_succ] using hq j
      · rintro ⟨p,hp0,hpLast,hp⟩
        refine ⟨p 1,?_,?_⟩
        · simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one,hp0] using hp 0
        · apply (ih (fun k => R k.succ) (p 1) y).mpr
          exact ⟨fun k => p k.succ,rfl,hpLast,
            fun k => by simpa only [Fin.castSucc_succ] using hp k.succ⟩

/-- A closed represented product gives literal cyclicly indexed points. -/
theorem cyclic_points_of_product {n : Nat} (hn : 0 < n)
    (R : Fin n → Relation M) (x : M)
    (h : relationProduct (List.ofFn R) x x) :
    ∃ p : Fin n → M, ∀ k, R k (p k) (p (cyclicNext hn k)) := by
  obtain ⟨q,hq0,hqLast,hq⟩ := (product_ofFn_iff n R x x).mp h
  refine ⟨fun k => q k.castSucc,?_⟩
  intro k
  have heq : q k.succ = q (cyclicNext hn k).castSucc := by
    by_cases hk : k.val + 1 = n
    · have hs : k.succ = Fin.last n := Fin.ext hk
      have hnxt : cyclicNext hn k = ⟨0,hn⟩ := by
        apply Fin.ext
        simp only [cyclicNext,hk,Nat.mod_self]
      rw [hs,hnxt,hqLast]
      exact hq0.symm
    · have hklt : k.val + 1 < n := by omega
      apply congrArg q
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc, cyclicNext, Nat.mod_eq_of_lt hklt]
  simpa only [heq] using hq k

end CCO.OwnerTransversal
