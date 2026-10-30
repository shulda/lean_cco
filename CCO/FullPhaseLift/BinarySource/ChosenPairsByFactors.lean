import CCO.FullPhaseLift.Full.Frozen
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! A complete chosen-pair lift directly from raw A03, even when the old
language does not distinguish unequal points by relation symbols. Freeze
every chosen complete zero-, one- and two-point object as an additional
full factor. Factor injectivity then prevents ALL global collisions.
These extra factors introduce no tuple of support at least three. -/

universe u v
namespace CCO.FullPhaseLift.BinarySource
open Canonical Full
noncomputable section

abbrev LowChart (V : Type u) := Σ k : Fin 3, (Fin k.val ↪ V)

def chosenLowFactor {L : Signature} {M : Type v} {V : Type u}
    (U : BoolTable L M) (D : Partial L V) (p : V ↪ M) (c : LowChart V) :
    FrozenFactor U (augmentLow U D p) where
  size := c.1.val
  inclusion := c.2
  table := pullback U (p ∘ c.2)
  age := ⟨embeddingOf (p ∘ c.2) (p.injective.comp c.2.injective) (fun _ _ => rfl)⟩
  agrees r xs := augmentLow_small U D p r (c.2 ∘ xs)
    ((smallSupport_fin (Nat.le_of_lt_succ c.1.isLt) xs).comp c.2)

/-- No point-separation premise is needed. In particular this applies to
the empty original language as well as the actual canonical expansion. -/
theorem lift_chosen_pairs_by_factors {L : Signature} {M : Type v}
    (U : BoolTable L M) (normal : SupportNormal U)
    (n : ℕ) (D : Partial L (Fin n)) (m : ℕ) (F : Fin m → FrozenFactor U D)
    (covered : HigherCovered F) (p : Fin n ↪ M) (hp : LowRealizes U D p) :
    ∃ q : Fin n ↪ M, Realizes U D q ∧ (∀ j, (F j).FixedBy q) ∧
      ∀ r xs, SmallSupport xs → U r (q ∘ xs) = U r (p ∘ xs) := by
  classical
  let D' := augmentLow U D p
  let κ := Fin m ⊕ LowChart (Fin n)
  letI : Fintype κ := Fintype.ofFinite κ
  let enum := Fintype.equivFin κ
  let factors : κ → FrozenFactor U D' := fun j => match j with
    | .inl i => (F i).augment p hp
    | .inr c => chosenLowFactor U D p c
  let family : Fin (Fintype.card κ) → FrozenFactor U D' := fun i => factors (enum.symm i)
  have fam (j : κ) : family (enum j) = factors j := by
    change factors (enum.symm (enum j)) = factors j
    rw [enum.symm_apply_apply]
  have hcov : HigherCovered family := by
    intro r xs b hd hs
    have hcov' := higherCovered_augment F covered p hp
    obtain ⟨i,hi⟩ := hcov' r xs b hd hs
    refine ⟨enum (.inl i),?_⟩
    rw [fam]
    exact hi
  have hpair : PairCompletion U D' family := by
    refine ⟨p,?_,?_⟩
    · intro r xs b hs hd
      change augmentLow U D p r xs = some b at hd
      rw [augmentLow_small U D p r xs hs] at hd
      exact Option.some.inj hd
    · intro j
      exact p.injective.comp (family j).inclusion.injective
  obtain ⟨q,hq,hfix⟩ := normal n D' _ family (augmentLow_consistent U D p) hcov hpair
  have hqi : Function.Injective q := by
    intro a b hab
    by_contra hne
    let j : Fin 2 ↪ Fin n := ⟨![a,b],by
      intro i k hik
      fin_cases i <;> fin_cases k <;> simp_all⟩
    let c : LowChart (Fin n) := ⟨⟨2,by decide⟩,j⟩
    have hf := (hfix (enum (.inr c))).1
    rw [fam] at hf
    change Function.Injective (q ∘ j) at hf
    have he : (0 : Fin 2) = 1 := hf (by exact hab)
    exact (by decide : (0 : Fin 2) ≠ 1) he
  let q' : Fin n ↪ M := ⟨q,hqi⟩
  refine ⟨q',?_,?_,?_⟩
  · intro r xs b hd
    exact hq r xs b (augmentLow_extends U D p hp r xs b hd)
  · intro j
    have h := hfix (enum (.inl j))
    rw [fam] at h
    exact h
  · intro r xs hs
    exact hq r xs _ (augmentLow_small U D p r xs hs)

end
end CCO.FullPhaseLift.BinarySource
