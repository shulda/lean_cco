import CCO.FullPhaseLift.BinarySource.CanonicalNames
import CCO.FullPhaseLift.Full.Partial

/-! Exact canonical pair-name preservation from every old low-support
truth value plus injectivity. Equality is logical equality throughout. -/

universe u v
namespace CCO.FullPhaseLift.BinarySource
open Canonical Full
noncomputable section

theorem names_of_lowEquivalent {L : Signature} {M : Type u} {V : Type v}
    (U : BoolTable L M) (hsym : SameSortSymmetric U) (q p : V ↪ M)
    (low : ∀ r xs, SmallSupport xs → U r (q ∘ xs) = U r (p ∘ xs)) :
    (∀ x, (pairTable U hsym).owner (q x) = (pairTable U hsym).owner (p x)) ∧
      ∀ x y, (pairTable U hsym).colour (q x) (q y) =
        (pairTable U hsym).colour (p x) (p y) := by
  classical
  have hu (x : V) : unaryProfile U (q x) = unaryProfile U (p x) := by
    funext a
    change U a.1 ((fun _ => q x) ∘ a.2) = U a.1 ((fun _ => p x) ∘ a.2)
    exact low a.1 (fun _ => x) (fun _ _ _ => Or.inl rfl)
  have hp (x y : V) : pairProfile U (q x) (q y) = pairProfile U (p x) (p y) := by
    funext a
    have hs : SmallSupport (![x,y] ∘ a.2) :=
      (smallSupport_fin (show 2 ≤ 2 from le_rfl) a.2).comp ![x,y]
    have h := low a.1 (![x,y] ∘ a.2) hs
    have hq : (q : V → M) ∘ (![x,y] ∘ a.2) = ![q x,q y] ∘ a.2 := by
      funext i
      change q (![x,y] (a.2 i)) = ![q x,q y] (a.2 i)
      generalize a.2 i = j
      fin_cases j <;> rfl
    have hp : (p : V → M) ∘ (![x,y] ∘ a.2) = ![p x,p y] ∘ a.2 := by
      funext i
      change p (![x,y] (a.2 i)) = ![p x,p y] (a.2 i)
      generalize a.2 i = j
      fin_cases j <;> rfl
    change U a.1 (![q x,q y] ∘ a.2) = U a.1 (![p x,p y] ∘ a.2)
    rwa [hq,hp] at h
  constructor
  · intro x
    apply Subtype.ext
    exact hu x
  · intro x y
    change taggedColour (source U hsym) (pack U (q x)) (pack U (q y)) =
      taggedColour (source U hsym) (pack U (p x)) (pack U (p y))
    apply tagCode_injective U
    rw [tagCode_pack,tagCode_pack]
    simp only [hu,hp,q.injective.eq_iff,p.injective.eq_iff]

end
end CCO.FullPhaseLift.BinarySource
