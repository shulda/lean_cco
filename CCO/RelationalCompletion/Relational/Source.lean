import CCO.RelationalCompletion.Relational.Unfolding
import Mathlib.Basic.Countable.Defs

universe u v
namespace CCO.RelationalCompletion.Relational.Structure
variable {L : Language.{u}} {V W : Type v}

/-- Explicit negative declarations distinguish a partial source diagram from
an induced complete factor. They never supply an embedding assumption. -/
structure Declarations (A : Structure L V) where
  negative : {n : ℕ} → L.Rel n → (Fin n → V) → Prop
  consistent : ∀ {n} (R : L.Rel n) xs, A.rel R xs → ¬ negative R xs

/-- Every relation instance on this factor, including nullaries, is explicitly
positive or explicitly negative. No source relation reflection is asserted. -/
def Declarations.CompleteOn {A : Structure L V} (D : Declarations A) (S : Set V) : Prop :=
  ∀ {n} (R : L.Rel n) xs, (∀ i, xs i ∈ S) → A.rel R xs ∨ D.negative R xs

theorem Declarations.negative_iff_not_positive {A : Structure L V}
    (D : Declarations A) {S : Set V} (hc : D.CompleteOn S) {n}
    (R : L.Rel n) xs (hx : ∀ i, xs i ∈ S) : D.negative R xs ↔ ¬ A.rel R xs := by
  constructor
  · intro hn hp
    exact D.consistent R xs hp hn
  · intro hp
    exact (hc R xs hx).resolve_left hp

/-- The source's finite-family/countable-target specialization. The core is
stronger: countability and completeness of the marked factors are unused.
The conclusion is an injective HE and ACTUAL separate target-image isomorphisms;
it is not a source-factor embedding, a fixed-position assertion, or a joint
image-union isomorphism. -/
theorem finite_family_unfolding (A : Structure L V) (U : Structure L W)
    [Finite V] [Countable W] (hom : U.Homogeneous) (sap : U.AgeSAP)
    (h : V → W) (hh : A.IsHE U h) {m : ℕ} (S : Fin m → Set V)
    (hinj : ∀ i, Set.InjOn h (S i)) :
    ∃ k : V → W, A.IsHE U k ∧ Function.Injective k ∧
      ∀ i, Nonempty (Iso (U.induce (h '' S i)) (U.induce (k '' S i))) := by
  obtain ⟨k, hk, hki, hkt⟩ := collision_unfolding A U hom sap h hh S hinj
  exact ⟨k, hk, hki, fun i => ⟨SameImageType.imageIso (hkt i) (hinj i) hki.injOn⟩⟩

/-- C16: already injective sources need no modification, including empty and
singleton carriers. This statement requires neither SAP nor homogeneity. -/
theorem already_injective (A : Structure L V) (U : Structure L W)
    (h : V → W) (hh : A.IsHE U h) (hi : Function.Injective h)
    {ι : Type*} (S : ι → Set V) :
    ∃ k : V → W, A.IsHE U k ∧ Function.Injective k ∧
      (k = h) ∧ ∀ i, U.SameImageType h k (S i) :=
  ⟨h, hh, hi, rfl, fun _ => SameImageType.refl⟩

/-- C15, the actual source-shaped statement: countable homogeneous target,
strong age amalgamation, finite partial source and finite family of explicitly
COMPLETE distinguished factors. Only their assumed h-injectivity is used by
the stronger underlying proof; completeness does not become source reflection. -/
theorem collision_unfolding_source (A : Structure L V) (U : Structure L W)
    [Finite V] [Countable W] (hom : U.Homogeneous) (sap : U.AgeSAP)
    (D : Declarations A) (h : V → W) (hh : A.IsHE U h)
    {m : ℕ} (S : Fin m → Set V) (_complete : ∀ i, D.CompleteOn (S i))
    (hinj : ∀ i, Set.InjOn h (S i)) :
    ∃ k : V → W, A.IsHE U k ∧ Function.Injective k ∧
      ∀ i, Nonempty (Iso (U.induce (h '' S i)) (U.induce (k '' S i))) :=
  finite_family_unfolding A U hom sap h hh S hinj

end CCO.RelationalCompletion.Relational.Structure
