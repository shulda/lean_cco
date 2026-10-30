import CCO.FullPhaseLift.BinarySource.ActualExtension

/-! Two actual complete FULL factors in a strict pair amalgam give a
support-normal signed partial diagram. Every positive and negative old
tuple on either factor is frozen, including all repeated/nullary tuples. -/

universe u v
namespace CCO.FullPhaseLift.BinarySource
open Canonical Full
noncomputable section
variable {L : Signature} {M : Type u} {V : Type v} {a b : ℕ}

def spanLeftFactor (U : BoolTable L M)
    (j : Fin a ↪ V) (q : Fin a ↪ M) (k : Fin b ↪ V) (p : Fin b ↪ M) :
    FrozenFactor U (unionPartial U j q k p) where
  size := a
  inclusion := j
  table := pullback U q
  age := ⟨embeddingOf q q.injective (fun _ _ => rfl)⟩
  agrees := unionPartial_left U j q k p

def spanRightFactor (U : BoolTable L M)
    (j : Fin a ↪ V) (q : Fin a ↪ M) (k : Fin b ↪ V) (p : Fin b ↪ M)
    (compatible : ∀ r (ys : Fin (L.arity r) → Fin a) (zs : Fin (L.arity r) → Fin b),
      j ∘ ys = k ∘ zs → U r (q ∘ ys) = U r (p ∘ zs)) :
    FrozenFactor U (unionPartial U j q k p) where
  size := b
  inclusion := k
  table := pullback U p
  age := ⟨embeddingOf p p.injective (fun _ _ => rfl)⟩
  agrees := unionPartial_right U j q k p compatible

def spanFactors (U : BoolTable L M)
    (j : Fin a ↪ V) (q : Fin a ↪ M) (k : Fin b ↪ V) (p : Fin b ↪ M)
    (compatible : ∀ r (ys : Fin (L.arity r) → Fin a) (zs : Fin (L.arity r) → Fin b),
      j ∘ ys = k ∘ zs → U r (q ∘ ys) = U r (p ∘ zs)) :
    Fin 2 → FrozenFactor U (unionPartial U j q k p) :=
  ![spanLeftFactor U j q k p,spanRightFactor U j q k p compatible]

theorem spanFactors_covered (U : BoolTable L M)
    (j : Fin a ↪ V) (q : Fin a ↪ M) (k : Fin b ↪ V) (p : Fin b ↪ M)
    (compatible : ∀ r (ys : Fin (L.arity r) → Fin a) (zs : Fin (L.arity r) → Fin b),
      j ∘ ys = k ∘ zs → U r (q ∘ ys) = U r (p ∘ zs)) :
    HigherCovered (spanFactors U j q k p compatible) := by
  intro r xs c hd _
  rcases unionPartial_specified U j q k p r xs c hd with ⟨ys,hys,_⟩ | ⟨ys,hys,_⟩
  · refine ⟨0,?_⟩
    rintro x ⟨i,rfl⟩
    exact ⟨ys i,congrFun hys i⟩
  · refine ⟨1,?_⟩
    rintro x ⟨i,rfl⟩
    exact ⟨ys i,congrFun hys i⟩

/-- The supplied strict actual pair target realizes every low-support
declaration on both legs; no full amalgam has been assumed. -/
theorem span_lowRealizes (U : BoolTable L M) (hsym : SameSortSymmetric U)
    (j : Fin a ↪ V) (q : Fin a ↪ M) (k : Fin b ↪ V) (p : Fin b ↪ M)
    (target : V ↪ M)
    (left : ∀ x y, (pairTable U hsym).colour (q x) (q y) =
      (pairTable U hsym).colour (target (j x)) (target (j y)))
    (right : ∀ x y, (pairTable U hsym).colour (p x) (p y) =
      (pairTable U hsym).colour (target (k x)) (target (k y))) :
    LowRealizes U (unionPartial U j q k p) target := by
  intro r xs c hs hd
  unfold unionPartial at hd
  cases hj : frozenPartial U j q r xs with
  | some d =>
    rw [hj] at hd
    obtain rfl := Option.some.inj hd
    exact base_lowRealizes U hsym j target q left r xs d hs hj
  | none =>
    rw [hj] at hd
    exact base_lowRealizes U hsym k target p right r xs c hs hd

end
end CCO.FullPhaseLift.BinarySource
