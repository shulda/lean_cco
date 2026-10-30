import CCO.ResetOrder.Composition

universe u v
namespace CCO.ResetOrder.Generic
variable {S : Type u}

theorem identity_relativeEP (L : Language S) (K : Age.{u,v} L) :
    RelativeEP (Reduct.identity L) K K := by
  intro A hA
  refine ⟨A, hA, ?_⟩
  intro E
  exact ⟨(Structure.Embedding.identity A.data).cast rfl E.reduct_eq.symm⟩

/-- The actual composed signature map from level n down to level zero. -/
def towerReduct (languages : ℕ → Language S)
    (steps : (i : ℕ) → Reduct (languages i) (languages (i + 1))) :
    (n : ℕ) → Reduct (languages 0) (languages n)
  | 0 => Reduct.identity (languages 0)
  | n + 1 => (towerReduct languages steps n).compose (steps n)

/-- Only the finitely many levels and gates up to n are assumed. -/
theorem relativeEP_finite_tower (languages : ℕ → Language S)
    (classes : (i : ℕ) → Age.{u,v} (languages i))
    (steps : (i : ℕ) → Reduct (languages i) (languages (i + 1)))
    (n : ℕ)
    (hH : ∀ i, i ≤ n → Hereditary (languages i) (classes i))
    (hM : ∀ i, i < n → MapsClass (steps i) (classes (i + 1)) (classes i))
    (hG : ∀ i, i < n → RestrictionGate (steps i) (classes (i + 1)) (classes i))
    (hEP : ∀ i, i < n → RelativeEP (steps i) (classes (i + 1)) (classes i)) :
    RelativeEP (towerReduct languages steps n) (classes n) (classes 0) := by
  induction n with
  | zero => exact identity_relativeEP (languages 0) (classes 0)
  | succ n ih =>
    have hprev := ih
      (fun i hi => hH i (Nat.le_succ_of_le hi))
      (fun i hi => hM i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      (fun i hi => hG i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      (fun i hi => hEP i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    exact foundational_relative_EP_composition (towerReduct languages steps n) (steps n)
      (hH (n + 1) (Nat.le_refl _)) (hM n (Nat.lt_succ_self n))
      (hG n (Nat.lt_succ_self n)) (hEP n (Nat.lt_succ_self n)) hprev

theorem relation_only_relativeEP_finite_tower (languages : ℕ → Language S)
    (classes : (i : ℕ) → Age.{u,v} (languages i))
    (steps : (i : ℕ) → Reduct (languages i) (languages (i + 1)))
    (n : ℕ)
    (hH : ∀ i, i ≤ n → Hereditary (languages i) (classes i))
    (hM : ∀ i, i < n → MapsClass (steps i) (classes (i + 1)) (classes i))
    (hF : ∀ i, i < n → (steps i).KeepsFunctions)
    (hEP : ∀ i, i < n → RelativeEP (steps i) (classes (i + 1)) (classes i)) :
    RelativeEP (towerReduct languages steps n) (classes n) (classes 0) :=
  relativeEP_finite_tower languages classes steps n hH hM
    (fun i hi => relation_only_restrictionGate (steps i) (hF i hi) _ _) hEP

end CCO.ResetOrder.Generic
