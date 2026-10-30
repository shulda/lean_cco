import CCO.FullPhaseLift.Canonical.Signature

/-! The actual partial FULL diagram obtained by freezing one finite base.
Tuples of EVERY arity entirely in the base are specified; all other tuples
are left unspecified. In particular all nullary tuples are retained. -/

universe u v w
namespace CCO.FullPhaseLift.BinarySource
open Canonical
noncomputable section
variable {L : Signature} {M : Type u} {V : Type v} {W : Type w}

def tuplePreimage {n : ℕ} (j : W ↪ V) (xs : Fin n → V)
    (h : ∀ i, xs i ∈ Set.range j) : Fin n → W :=
  fun i => Classical.choose (h i)

theorem tuplePreimage_spec {n : ℕ} (j : W ↪ V) (xs : Fin n → V)
    (h : ∀ i, xs i ∈ Set.range j) : j ∘ tuplePreimage j xs h = xs := by
  funext i
  exact Classical.choose_spec (h i)

theorem tuplePreimage_unique {n : ℕ} (j : W ↪ V) (xs : Fin n → W)
    (h : ∀ i, (j ∘ xs) i ∈ Set.range j) :
    tuplePreimage j (j ∘ xs) h = xs := by
  funext i
  exact j.injective (Classical.choose_spec (h i))

def frozenPartial (U : BoolTable L M) (j : W ↪ V) (q : W → M) :
    (r : Fin L.size) → (Fin (L.arity r) → V) → Option Bool := by
  classical
  exact fun r xs => if h : ∀ i, xs i ∈ Set.range j then
    some (U r (q ∘ tuplePreimage j xs h)) else none

theorem frozenPartial_on (U : BoolTable L M) (j : W ↪ V) (q : W → M)
    (r : Fin L.size) (xs : Fin (L.arity r) → W) :
    frozenPartial U j q r (j ∘ xs) = some (U r (q ∘ xs)) := by
  classical
  have h : ∀ i, (j ∘ xs) i ∈ Set.range j := fun i => ⟨xs i,rfl⟩
  simp only [frozenPartial,dite_eq_left h,tuplePreimage_unique]

theorem frozenPartial_specified (U : BoolTable L M) (j : W ↪ V) (q : W → M)
    (r : Fin L.size) (xs : Fin (L.arity r) → V) (b : Bool)
    (h : frozenPartial U j q r xs = some b) :
    ∃ ys : Fin (L.arity r) → W, j ∘ ys = xs ∧ U r (q ∘ ys) = b := by
  classical
  unfold frozenPartial at h
  split_ifs at h with hxs
  · exact ⟨tuplePreimage j xs hxs,tuplePreimage_spec j xs hxs,Option.some.inj h⟩

/-- Any map that extends the full base exactly realizes every declared
positive AND negative tuple of its frozen partial diagram. -/
theorem frozenPartial_realizes (U : BoolTable L M) (j : W ↪ V) (q : W → M)
    (f : V → M) (hf : ∀ x, f (j x) = q x)
    (r : Fin L.size) (xs : Fin (L.arity r) → V) (b : Bool)
    (h : frozenPartial U j q r xs = some b) : U r (f ∘ xs) = b := by
  obtain ⟨ys,hys,hb⟩ := frozenPartial_specified U j q r xs b h
  have he : f ∘ xs = q ∘ ys := by
    rw [← hys]
    funext i
    exact hf (ys i)
  rw [he]
  exact hb

/-- The two full factors are combined only after their ALL-arity data
agree on the entire overlap. Cross tuples remain unspecified. -/
def unionPartial {Y : Type*} (U : BoolTable L M)
    (j : W ↪ V) (q : W → M) (k : Y ↪ V) (p : Y → M) :
    (r : Fin L.size) → (Fin (L.arity r) → V) → Option Bool :=
  fun r xs => match frozenPartial U j q r xs with
    | some b => some b
    | none => frozenPartial U k p r xs

theorem unionPartial_left {Y : Type*} (U : BoolTable L M)
    (j : W ↪ V) (q : W → M) (k : Y ↪ V) (p : Y → M)
    (r : Fin L.size) (xs : Fin (L.arity r) → W) :
    unionPartial U j q k p r (j ∘ xs) = some (U r (q ∘ xs)) := by
  simp only [unionPartial,frozenPartial_on]

theorem unionPartial_right {Y : Type*} (U : BoolTable L M)
    (j : W ↪ V) (q : W → M) (k : Y ↪ V) (p : Y → M)
    (compatible : ∀ r (ys : Fin (L.arity r) → W) (zs : Fin (L.arity r) → Y),
      j ∘ ys = k ∘ zs → U r (q ∘ ys) = U r (p ∘ zs))
    (r : Fin L.size) (xs : Fin (L.arity r) → Y) :
    unionPartial U j q k p r (k ∘ xs) = some (U r (p ∘ xs)) := by
  classical
  by_cases h : ∀ i, (k ∘ xs) i ∈ Set.range j
  · simp only [unionPartial,frozenPartial,dite_eq_left h]
    exact congrArg some (compatible r _ xs (tuplePreimage_spec j (k ∘ xs) h))
  · simp only [unionPartial,frozenPartial,dite_eq_right h]
    exact frozenPartial_on U k p r xs

theorem unionPartial_specified {Y : Type*} (U : BoolTable L M)
    (j : W ↪ V) (q : W → M) (k : Y ↪ V) (p : Y → M)
    (r : Fin L.size) (xs : Fin (L.arity r) → V) (b : Bool)
    (h : unionPartial U j q k p r xs = some b) :
    (∃ ys : Fin (L.arity r) → W, j ∘ ys = xs ∧ U r (q ∘ ys) = b) ∨
    (∃ ys : Fin (L.arity r) → Y, k ∘ ys = xs ∧ U r (p ∘ ys) = b) := by
  unfold unionPartial at h
  cases hj : frozenPartial U j q r xs with
  | none =>
    rw [hj] at h
    exact Or.inr (frozenPartial_specified U k p r xs b h)
  | some a =>
    rw [hj] at h
    obtain rfl := Option.some.inj h
    exact Or.inl (frozenPartial_specified U j q r xs a hj)

/-- Strong pair amalgamation identifies exactly the FULL common base.
Its full induced embeddings therefore make the two declarations agree
on every overlap tuple, of arbitrary arity and with repetitions. -/
theorem overlap_compatible {Y Z : Type*} (U : BoolTable L M)
    (j : W ↪ V) (q : W → M) (k : Y ↪ V) (p : Y → M)
    (s : Z → W) (t : Z → Y)
    (intersection : ∀ x y, j x = k y → ∃ a, s a = x ∧ t a = y)
    (base : ∀ r (xs : Fin (L.arity r) → Z),
      U r (q ∘ (s ∘ xs)) = U r (p ∘ (t ∘ xs)))
    (r : Fin L.size) (ys : Fin (L.arity r) → W) (zs : Fin (L.arity r) → Y)
    (he : j ∘ ys = k ∘ zs) : U r (q ∘ ys) = U r (p ∘ zs) := by
  classical
  have h (i : Fin (L.arity r)) : ∃ a, s a = ys i ∧ t a = zs i :=
    intersection (ys i) (zs i) (congrFun he i)
  let xs : Fin (L.arity r) → Z := fun i => Classical.choose (h i)
  have hs : s ∘ xs = ys := funext (fun i => (Classical.choose_spec (h i)).1)
  have ht : t ∘ xs = zs := funext (fun i => (Classical.choose_spec (h i)).2)
  rw [← hs,← ht]
  exact base r xs

end
end CCO.FullPhaseLift.BinarySource
